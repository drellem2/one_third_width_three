# Standard Dominance: the comparison / deformation route

**Work item:** mg-4a86
**Deliverable:** map the comparison/decomposition/tempering route from Aldous
single-particle dominance (ambient `S_n` interchange) to the constrained BK chain
on `L(P)`; identify the best intermediate target and attempt it.

---

## §0 Executive verdict

Three findings, in decreasing order of consequence.

**1. The ticket's target statement is false, and I can prove it.** The route was
scoped as "lift Aldous dominance to get `λ₂^BK = λ_std`". That conclusion holds on
**0 / 195** posets at `n=4` and **0 / 4111** at `n=5` — nowhere — and fails
structurally on the class the programme treats as extremal (ordinal sums). It is
not a near-miss awaiting a better comparison argument, and it is not a
normalization slip (§2.5).

**2. The lift the ticket asks for already exists in the literature — and it does
not give dominance.** **Wilson (2004)**, generalizing Bubley–Dyer, proves that for
**every** `n`-element poset,

  `gap_BK(P) ≥ (1 − cos(π/n))/(n−1) = Θ(n^{-3})`,

which is *exactly* the free/antichain value — the unconstrained chain is the
**minimizer**, and adding poset relations never hurts the gap. I verified this on
all **4306** posets at `n ≤ 5`: **zero violations, bound attained exactly** (§4).

So the transfer "ambient single-particle bound ⟹ constrained chain" is a *solved
problem*, solved sharply, by direct path coupling rather than by comparison. And
having it changes nothing about standard dominance. This is the cleanest possible
demonstration of finding 3.

**3. The obstruction is a category mismatch, and it is upstream of the octopus.**

> `λ₂^BK` is a **dynamical** functional (the gap of a generator). `λ_std` is a
> **static** functional of the stationary measure alone. Every technique in the
> toolkit — decomposition, tempering, Diaconis–Saloff-Coste, censoring — produces
> inequalities between *Dirichlet forms*. None can have `λ_std` as an endpoint,
> because `λ_std` is not the gap of any chain in the family.

The ticket's anticipated crux — "the octopus's rerouting passes through
non-extensions, so the operator inequality does not restrict" — is a correct
statement about the octopus (§5.0), but it is **not the binding constraint**. A
programme organized around defeating it would be solving the wrong problem.

The sharpest evidence inverts the ticket's intuition: on the **antichain** the
constraint is empty, `L(P) = S_n`, the BK chain *is* the interchange process on
the path, and the Aldous/CLR lift is **exact** (verified to `5e-15`). That is
precisely where `λ_std`-dominance fails **maximally** (`λ_std = 0`,
`λ₂^BK → 1`). The lift working perfectly and dominance failing completely are the
*same case*.

**What survives.** The well-posed version of what the programme needs is not
SD-BK but the **overlap** form `SD-quant(c)` (§3.2). I measured its constant for
the first time: `c ≥ 0.979` across every poset tested at `n ≤ 6`, and `c ≈ 1` in
the informative stratum (§7). That is a genuine positive signal — with an
explicit, honest caveat about exactly where it is predicted to break (§7.3).

**Bottom line against the ticket's own success criterion** ("a clean, rigorous
'here is the reduction and here is exactly why it is not weaker' is a fully
successful outcome"): the boundary terms do **not** collapse to full standard
dominance — in the tempering case the term is identified exactly as `ρ(T)` (§6).
But no route yields a partial result *about dominance*, because dominance as
stated is false and is not in the image of any comparison method.

### Claim ledger

| # | Claim | Tag |
|---|---|---|
| C1 | `λ_std(antichain_n) = 0` while `λ₂^BK → 1`; dominance excess → 1 | **[proven]** (hand proof §2.1 + exact numerics) |
| C2 | `λ₂^BK = λ_std` holds for 0/195 (`n=4`) and 0/4111 (`n=5`) | **[proven]** (exhaustive) |
| C3 | `λ_std ≤ λ₂^BK` fails on **every** ordinal sum. ~~and **exactly** there~~ — **the "exactly" is FALSE for `n ≥ 7`** | `⟸` (all ordinal sums fail) **[proven]** ∀`n`. `⟹` (nothing else fails) **[REFUTED]** by `mg-d1be`: true `n ≤ 6` exhaustively, indecomposable violator at `n = 7`, **19 at `n = 8`** (16 of width exactly 3), exact certificates — a small-`n` coincidence, not a characterization (§2.4) |
| C4 | Ordinal sums: exact BK product formula; `λ_std = 1`; dominance fails on the whole class | **[proven]** (hand proof §2.3 + 9/9 numeric) |
| C5 | SD-BK is not a normalization slip (ratio spread 9.3×/18.8×, growing in `n`) | **[proven]** (§2.5) |
| C6 | One-particle sector `U` invariant on ambient `S_n`, **not** on `L(P)`; leakage `Θ(0.1)` | **[proven]** (§3.2) |
| C7 | Wilson's universal bound `gap_BK ≥ (1−cos(π/n))/(n−1)`, attained by the antichain | **[proven in the literature]** (Wilson 2004); **independently verified 0/4306 violations** (§4) |
| C8 | `lim_{β→∞} λ₂(β) = max(λ₂^BK, ρ(T))` (block-triangularity) | **[proven]** (§6.2) |
| C9 | Collar term dominates in 3/4 constrained cases ⇒ tempering limit ≠ BK | **[proven]** (numerics §6.2) |
| C10 | `SD-quant` constant `c ≥ 0.979` on all posets tested at `n ≤ 6` | **[proven for `n≤6`]**; [heuristic] beyond, and §7.3 flags where it should fail |
| C11 | No comparison technique can prove dominance (category mismatch) | **[heuristic]** — rigorous per-technique (§5), but not a formal quantifier over all methods |

---

## §1 Three inequivalent statements called "standard dominance"

The repo and the ticket use one name for three different things. Disentangling
them is most of the work; once separated the verdicts are immediate.

- **Transport / standard block** (`onethird_mgb0a6_spectral_killshot_probe.py:263-296`):
  `(T_P)_{x,a} = Pr_{σ~Unif L(P)}[σ(a) = x]`, `S_P = (T_P + T_Pᵀ)/2`,
  `λ_std(P) =` top eigenvalue of `S_P` on `H = 𝟙^⊥`.
  **Depends only on the measure `Unif L(P)`, not on any dynamics.**
- **BK chain** (`step1.tex:20-26`, `step8.tex:21-25`): lazy walk on `L(P)`, step
  `1/(2(n−1))` per adjacent incomparable position; `λ₂^BK` its second eigenvalue.
- **Cayley walk** (`onethird_mgb0a6_spectral_killshot_probe.py:459-475`): walk on
  **all of `S_n`** with generating measure `η_P = (μ_P + μ_P^∨)/2`, `μ_P` uniform
  on `L(P)` viewed as a set of permutations.

| Name | Statement | Status |
|---|---|---|
| **SD-Cayley** | `λ₂(Cayley walk) = λ_std` | ~~Empirically supported, **0/132** (`mgb0a6`).~~ ⚠️ **THE BARE FIGURE IS WITHDRAWN (mg-e2a0, landing mg-55f2 / mg-65f5 §1.5): `0/132` IS A SAMPLING ARTIFACT AND CARRIES ITS FRAME OR IT IS NOT QUOTED.** Read: **`0` failures in `mgb0a6`'s own frame — `n ≤ 6` exhaustive + `n = 7` **top-λ spot only** — a frame that excludes the known moderate-λ `n = 7` refuters (166, mg-8b64). Not a clean sweep.** Coherent and nontrivial, and §1.1 below is unaffected. *Scope note kept honest in both directions:* the 166 refuters are **BK-side**, so by this document's own §1.1 they refute **SD-BK**, not SD-Cayley — SD-Cayley is not refuted here. What is withdrawn is the figure's **strength**, which is `mgb0a6`'s frame in either reading. `STATE.md` row 3b. |
| **SD-BK** | `λ₂^BK = λ_std` | **FALSE** — 0/4306 (§2). *This is the ticket's target.* |
| **SD-quant** | the slowest BK mode has an `Ω(1)` component in the standard sector | Coherent; the programme's actual need. Measured here for the first time (§7). |

### 1.1 The "0/132" evidence does not support the ticket's target

The ticket asserts SD-BK is "empirically airtight (0/132 counterexamples)". **The
0/132 figure is SD-Cayley evidence and does not transfer.** The Cayley walk lives
on `S_n` with generating set `L(P)`; the BK chain lives on `L(P)` with
adjacent-transposition generators. Different state space, different generators.

SD-Cayley is also *near-automatic* in a way SD-BK is not: by Schur's lemma
`ρ_std(η_P) = S_P` exactly, so `λ_std` is **guaranteed** to sit in the Cayley
spectrum, and SD-Cayley only asserts no other irrep out-eigenvalues it. On `L(P)`
there is **no group action at all**, hence no irrep decomposition and no sector in
which `λ_std` is guaranteed to appear (§3.2). The repo already records a scope
correction (`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:290`: "**Standard
dominance is not universal**").

### 1.2 A second inherited error

`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:273-275` asserts

> "But `λ_std ≤ λ₂^{BK}` (the standard sector is a subspace)"

**False as stated**, and ~~precisely characterizable~~ **not characterizable**: it fails on
*every* ordinal sum (∀`n`, §2.3), and — contrary to what this document originally recorded —
it fails **off** the ordinal sums too, from `n = 7` on (§2.4, `mg-d1be`). The stated
justification is invalid regardless — it presupposes the standard sector embeds in
`L²(L(P))` as an invariant subspace making `λ_std` a Rayleigh restriction, which
it does not (§3.2).

This matters concretely: the inequality is used to argue Theorem E "bounds the gap
in the wrong direction". **That argument survives, on stronger ground** — see
[`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md`](OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md) §(d).
Since no universal inequality holds in *either* direction (the reverse fails on antichains,
§2.1, and the two are never equal, 0/4306), a bound on `λ₂^BK` carries **no information**
about `λ_std` — strictly stronger than a wrong-way inequality, which would at least have
been an inequality. What does *not* survive is the "off the ordinal sums" escape hatch: it
is not a hypothesis that saves anything, because it is false.

---

## §2 SD-BK is false

Reproduce: `python3.11 scripts/onethird_mg4a86_standard_dominance_target_audit.py`.

### 2.1 The antichain [proven]

Let `P = A_n`, so `L(P) = S_n`.

**`λ_std(A_n) = 0`.** By symmetry `Pr[σ(a)=x] = 1/n` for all `x,a`, so `T_P = J/n`
and `S_P = J/n`. On `H = 𝟙^⊥`, `J` acts as `0`. ∎

**`λ₂^BK(A_n) = 1 − (1−cos(π/n))/(n−1)`.** The BK chain on `L(A_n) = S_n` is
exactly the interchange process on the path `P_n` at rate `1/(2(n−1))` per edge;
by CLR its gap equals the single-particle gap. *(The disproof does not need CLR:
the `≥` direction is elementary. Take `f(σ) = g(σ^{-1}(x₀))` for fixed `x₀` and
`g` the path's Fiedler vector — a one-particle observable whose BK Dirichlet form
is exactly the single-particle one, so `λ₂^BK ≥ 1 − (1−cos(π/n))/(n−1)` by
Rayleigh, contradicting `λ₂^BK = λ_std = 0` for `n ≥ 3`.)*

| `n` | `λ₂^BK` | single-particle | residual | `λ_std` | excess |
|---|---|---|---|---|---|
| 3 | 0.750000000 | 0.750000000 | 0.0 | 0 | **0.750** |
| 4 | 0.902368927 | 0.902368927 | 5.6e-16 | 0 | **0.902** |
| 5 | 0.952254249 | 0.952254249 | 1.1e-15 | 0 | **0.952** |
| 6 | 0.973205081 | 0.973205081 | 2.1e-15 | 0 | **0.973** |
| 7 | 0.983494811 | 0.983494811 | 5.2e-15 | 0 | **0.983** |

**This inverts the ticket's premise.** The antichain is where the constraint is
*empty* and the Aldous lift is *exact*. The ticket expected the obstruction to
live where the constraint bites; instead the obstruction is maximal where the
constraint vanishes. So the obstruction is not about the constraint at all.

### 2.2 Exhaustive: dominance holds nowhere [proven]

| `n` | tested | `λ₂^BK = λ_std` | fails | `λ_std > λ₂^BK` | worst excess |
|---|---|---|---|---|---|
| 4 | 195 | **0** | 195 | 33 | 0.902368927 |
| 5 | 4111 | **0** | 4111 | 550 | 0.952254249 |

Not one instance in 4306; the failure is two-sided.

### 2.3 Ordinal sums: an exact theorem [proven]

The programme's characterization is `λ_std = 1` **iff** `P` is an ordinal sum
(`OneThird-L1b-ExpectedRank-Certificate.md:53-56`), so ordinal sums are the
extremal class the near-ordinal-sum programme is organized around.

> **Theorem (ordinal-sum product formula).** Let `P = P₁ ⊕ ⋯ ⊕ P_k`, `|P_i| = n_i`,
> `n = Σ n_i`. Then
> 1. `L(P) = L(P₁) × ⋯ × L(P_k)` by concatenation, and the BK graph on `L(P)` is
>    the **Cartesian product** of the BK graphs on the `L(P_i)`;
> 2. `gap_BK(P) = min_i gap_BK(P_i) · (n_i − 1)/(n − 1)`;
> 3. `λ_std(P) = 1`.
>
> **Corollary.** For every ordinal sum with a block that is neither a singleton
> nor a chain, `gap_BK(P) > 0 = 1 − λ_std(P)`. **SD-BK fails on the entire class
> of nontrivial ordinal sums**, with `λ_std > λ₂^BK` there.

*Proof of (1).* In an ordinal sum two elements are incomparable only if in the
same block, so an adjacent pair of a linear extension is swappable only if both
members lie in one block: every BK move is internal to a block and blocks never
interleave. ∎ *(2) follows since the generator is then a direct sum and a chain's
gap is linear in its step rate.*

**Verified**, 9/9 families, formula exact to `1e-9`:

| ordinal sum | `\|L(P)\|` | gap actual | gap predicted | `λ_std` | SD-BK? |
|---|---|---|---|---|---|
| `A₃ ⊕ A₃` | 36 | 0.100000000 | 0.100000000 | 1.000000 | NO |
| `A₂ ⊕ A₂` | 4 | 0.333333333 | 0.333333333 | 1.000000 | NO |
| `A₂ ⊕ A₃` | 12 | 0.125000000 | 0.125000000 | 1.000000 | NO |
| `A₂ ⊕ A₂ ⊕ A₂` | 8 | 0.200000000 | 0.200000000 | 1.000000 | NO |
| `A₄ ⊕ C₁` | 24 | 0.073223305 | 0.073223305 | 1.000000 | NO |
| `V₃ ⊕ A₂` | 4 | 0.250000000 | 0.250000000 | 1.000000 | NO |

*(6 of the 9 families shown; `|L(P)| = Π|L(P_i)|` confirmed on all. Full table in
the JSON certificate.)*

On ordinal sums `λ_std = 1 > λ₂^BK`; on antichains `λ_std = 0 < λ₂^BK`. The two
extremal classes straddle the claimed equality from opposite sides — any putative
proof of SD-BK would have to be false at both ends.

### 2.4 Where the weak inequality fails — a small-`n` coincidence, **not** a characterization [REFUTED beyond `n = 6`]

> **⚠ SCOPE CORRECTION (`mg-d1be`, landed 2026-08-07; recorded here by `mg-24eb`).** The
> "**exactly** the ordinal sums" reading below is **false for `n ≥ 7`** and breaks
> **wholesale** at `n = 8`. It is a small-`n` coincidence, not a theorem with exceptions —
> a reader who thinks it is "true with exceptions" will keep reaching for it; it does not
> survive to be reached for. Only the `⟸` half (every ordinal sum violates) is a theorem
> ∀`n`; the `⟹` half (nothing else violates) is dead. Details and both exact certificates:
> [`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md`](OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md) §(e).

| `n` | posets | `λ_std > λ₂^BK` | `λ_std = 1` | **sets equal?** | sym. difference |
|---|---|---|---|---|---|
| 4 | 195 | 33 | 33 | **YES** | 0 |
| 5 | 4111 | 550 | 550 | **YES** | 0 |

> **Proposition (`n ≤ 6` only — does NOT extend).** For every labeled poset on `n ≤ 5`
> with `|L(P)| ≥ 2` (extended to `n ≤ 6` up to isomorphism by `mg-d1be`):
> `λ_std > λ₂^BK` ⟺ `λ_std = 1` ⟺ `P` is an ordinal sum. Equivalently,
> ~~**`λ_std ≤ λ₂^BK` holds precisely off the ordinal sums.**~~ — **true at `n ≤ 6`,
> FALSE at every `n ≥ 7` we can check.**

`⟸` is the §2.3 Corollary, **proven for all `n`**. `⟹` is **false**: it is verified
exhaustively at `n = 4,5` (and at `n = 6` by `mg-d1be`), and **refuted at `n = 7` and
`n = 8`**. `mg-d1be` re-ran the set equality over every poset up to isomorphism through
`n = 6` (enumerator self-checked against 1, 2, 5, 16, 63, 318 classes) and then two sizes
further, at width `≤ 3`:

| scan | classes | violations | ordinal sums | sym. diff. | **indecomposable violators** |
|---|---|---|---|---|---|
| all posets, `n = 4` | 15 | 8 | 8 | 0 | 0 |
| all posets, `n = 5` | 62 | 31 | 31 | 0 | 0 |
| all posets, `n = 6` | 317 | 133 | 133 | 0 | 0 |
| width ≤ 3, `n = 7` | 1284 | 538 | 537 | **1** | **1** (width 2) |
| width ≤ 3, `n = 8` | 7789 | 2876 | 2857 | **19** | **19** — of which **16 have width exactly 3** |

The set equality holds through `n = 6`, takes its **first** hit at `n = 7`, and **breaks
wholesale at `n = 8`** (19 exceptions in one sweep). Both witnesses are **indecomposable**
(their incomparability graphs are connected, so they are not ordinal sums) and 16 of the
`n = 8` ones have **width exactly 3** — so neither indecomposability nor the width-3
restriction rescues the claim. Each is certified by an **exact** separating rational
(`9437/10000` at `n = 7`, `243/250` at `n = 8`): `λ₂^BK ≤ c` by exact PSD elimination,
`λ_std > c` by an exact rational Rayleigh quotient. Witnesses and certificates:
[`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md`](OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md) §(e)
— not restated here, and neither sweep should be re-run (7789 classes at `n = 8` is not a
cheap re-derivation, and it is already exact).

**So the earlier framing — "fairer to the repo than *the inequality is false*: it is true
generically and fails on a thin, exactly-identified set" — is withdrawn.** The set is not
exactly identified. What survives is: the inequality fails on **all** ordinal sums (∀`n`,
§2.3), and on an unidentified further set that is empty at `n ≤ 6` and non-empty from
`n = 7` on.

**Why this looked promising and why it never could have paid** (`mg-d1be`, the sharpest
form of the point): at every exhaustively checkable size the direction that *would* have
helped, `λ_std ≥ λ₂^BK`, holds exactly on the ordinal sums — i.e. exactly where
`λ_std = 1` and the downstream target is already trivially true. **The helpful direction is
available only where it is vacuous.** (At the `n = 7` violator it holds non-vacuously, so
it is not *universally* vacuous — but it is not universal either.)

### 2.5 SD-BK is not a normalization slip [proven]

The obvious objection is that SD-BK is really an equality up to a constant. It is
not: `gap_BK / (1 − λ_std)` over posets with `λ_std < 1` has

| `n` | min | max | spread |
|---|---|---|---|
| 4 | 0.097631 | 0.905309 | **9.3×** |
| 5 | 0.047746 | 0.898890 | **18.8×** |

A single constant would give spread `1.0`. The spread **grows with `n`**,
consistent with §3.1's scaling mismatch.

---

## §3 Why: static-vs-dynamic, not constrained-vs-ambient

### 3.1 Different objects, different scaling [proven]

Aldous/CLR controls the single-particle walk **on the graph** — a functional of
the *generator*. `λ_std` is the top eigenvalue of the symmetrized *stationary
marginal* matrix — a functional of the *measure*. On the antichain they do not
even scale alike:

- transport gap `1 − λ_std(A_n) = 1` — **`Θ(1)`**;
- BK gap `1 − λ₂^BK(A_n) = (1−cos(π/n))/(n−1) ≍ π²/(2n³)` — **`Θ(n^{-3})`**.

No constant reconciles `Θ(1)` with `Θ(n^{-3})`. The ticket's phrase "one-particle
/ standard-representation object" silently identifies two different things.

### 3.2 There is no standard sector on `L(P)` [proven]

On `S_n` the span `U = span{ σ ↦ 𝟙[σ(a)=x] }` is **invariant** under the
interchange process (a move permutes the position index `a`). That invariance is
what makes "the gap lives in the standard sector" well-posed and is what Schur/CLR
exploit. On `L(P)` the move at position `i` fires only when `σ(i), σ(i+1)` are
incomparable — the action on the position index is **`σ`-dependent** — so `U` need
not be invariant. Measure

  `leak(P) := ‖ (I − P_U) W P_U ‖_op`,   zero iff `U` is BK-invariant:

| poset | `\|L(P)\|` | `dim U` | leakage |
|---|---|---|---|
| antichain-4 *(control: ambient `S_n`)* | 24 | 10 | **9.5e-16** |
| antichain-5 *(control: ambient `S_n`)* | 120 | 17 | **1.5e-15** |
| N-poset (2+2) | 6 | 5 | **1.44e-01** |
| chain2+anti2 | 12 | 8 | **1.44e-01** |
| V + isolated | 8 | 6 | **1.00e-01** |

Controls confirm the implementation: on the antichain leakage is machine-zero and
`dim U = (n−1)²+1` exactly (10, 17, 5 at `n=4,5,3`). On constrained posets leakage
is **`Θ(0.1)`**.

**Consequence.** There is no invariant standard sector on `L(P)`, hence no
guarantee `λ_std` appears in the BK spectrum at all — which is why SD-BK fails in
*both* directions. The correct formulation of the programme's need is an
**overlap** statement, well-posed without invariance:

  **`SD-quant(c)`**: the top nontrivial BK eigenfunction `f` satisfies
  `‖P_U f‖² ≥ c‖f‖²`.

Measured in §7.

---

## §4 The lift already exists — Wilson (2004) — and it does not help

This is the decisive literature finding, and it was not anticipated by the ticket.

> **Theorem (Karzanov–Khachiyan chain; Wilson 2004, Table 1 + Prop. 3, building on
> Bubley–Dyer 1999).** For **every** `n`-element poset `P`, the
> adjacent-transposition chain on `L(P)` satisfies
> `gap_BK(P) ≥ (1 − cos(π/n))/(n−1) = Θ(n^{-3})`,
> the free/antichain value. The unconstrained chain is the **minimizer**: adding
> poset relations never decreases the gap. Sometimes tight.

Wilson obtains this by direct path coupling with **sinusoidal** weights
`w(i) = cos(β(i/n − 1/2))`, treating blocked swaps as no-ops — *not* by comparison
with the free chain. That is stronger than a comparison argument would be, since
it is sharp.

**Independently verified here**, exhaustively:

| `n` | bound `(1−cos(π/n))/(n−1)` | min `gap_BK` over all posets | violations | attained exactly? |
|---|---|---|---|---|
| 4 | 0.097631073 | 0.097631073 | **0 / 195** | **yes** |
| 5 | 0.047745751 | 0.047745751 | **0 / 4111** | **yes** |

**Why this matters more than any of the four techniques.** The ticket's programme
was: transport an ambient single-particle bound to the constrained chain. **That
is done, sharply, and has been since 2004.** And it yields nothing about standard
dominance — because `λ_std` never appears in it. If a *sharp, universal,
already-proven* lift of exactly the anticipated form does not produce dominance,
no lossy comparison version will either.

*Citation caveat, honoring the source check:* Wilson states this in **Table 1**
(row "Linear extensions of partially ordered set, Karzanov–Khachiyan chain",
spectral-gap column), following from the §6 contraction at `β = π` via his
Proposition 3 (Wasserstein contraction ⇒ gap, after Chen 1998). It is **not a
numbered theorem** in the paper. Cite Table 1 + Prop. 3, or reprove the one-line
step. The `Ω(n^{-3})` *order* predates Wilson (Bubley–Dyer §4); Wilson supplies
the sharp constant. A matching *upper* bound is **not** universal — constrained
posets can have far larger gaps, as §2 confirms.

---

## §5 The four techniques: boundary terms and classification

Classification per the ticket: **(a)** still full standard dominance;
**(b)** strictly weaker / checkable; **(c)** tractable on a sub-class.

### 5.0 The octopus, stated precisely, and why it does not restrict

For completeness, since the ticket centers on it. In `ℝ[S_n]`, with head vertex
`n`, weights `w_{in} ≥ 0`, `S = Σ_k w_{kn}` (Cesi 2016, Thm 4.2, equivalent to
CLR Thm 2.3):

  `Σ_{i<n} w_{in}(Id − (i n)) ⪰ (1/S) Σ_{i<k<n} w_{in}w_{kn}(Id − (i k))`

as self-adjoint operators in the regular representation. The LHS is the star at
the head; the RHS its star–mesh transform.

**Why it does not restrict to `L(P)`.** The inequality is an operator relation in
`ℝ[S_n]`, valid in *every* representation — but its meaning requires the `S_n`
action. Confinement to `L(P)` is the projection `Π` onto `span{δ_σ : σ ∈ L(P)}`,
and `Π` does **not commute** with the `τ_{ij}`: `τ_{ij}` maps a linear extension
to a non-extension whenever `i,j` are comparable. So `Π A Π ⪰ Π B Π` does not
follow from `A ⪰ B`. **This is correct and I found no way around it** — but §4
shows it is not the binding obstruction, since the conclusion the octopus would
buy is already available by other means.

### 5.1 State-space decomposition (Madras–Randall 2002; JSTV 2004) — **[blocked]**

Slice `S_n` by violation count: `Ω_k = {σ : V(σ) = k}`, `Ω_0 = L(P)`, the
restriction to which is exactly BK.

**Two independent failures.**

*(i) The inequality points the wrong way.* Madras–Randall Thm 1.1 gives
`Gap(full) ≥ Θ^{-2} · Gap(projection) · min_i Gap(restriction_i)` — it
**lower-bounds the full chain** by its pieces. Here the *hard* chain is the
restriction (BK) and the *easy* one is the full chain (Aldous). Decomposition
bounds a hard chain by easy pieces; we need the converse. Knowing `Gap(full)`
places no lower bound on any restriction — a single slice can be arbitrarily slow
while the whole mixes fine.

*(ii) Madras–Randall is literally vacuous for this slicing.* MR Thm 1.1 is an
**overlapping-cover** theorem: on a disjoint partition `π[A_i ∩ A_j] = 0`, so
`P_H = Id` and `Gap(P_H) = 0`. Slicing by violation count **is** a disjoint
partition, so the bound reads `Gap ≥ 0`. For disjoint partitions one needs
**Martin–Randall** or **JSTV**, whose escape parameter
`γ = max_i max_{x∈Ω_i} Σ_{y∉Ω_i} P(x,y)` gives
`λ ≥ min{λ̄/3, λ̄λ_min/(3γ + λ̄)}` — still direction *(i)*.

**Boundary term:** the projection chain on violation levels.
**Classification: blocked** — structurally inapplicable in this direction.
*(A cleaner "no" than anticipated: the term does not collapse to dominance; the
method does not point this way.)*

*Attribution note:* MR Thm 1.1 is proved via **Caracciolo–Pelissetto–Sokal**
(1992, unpublished, reproduced in MR Appendix A); "Madras–Randall" is a
first-*publication* attribution.

### 5.2 Simulated tempering / soft-constraint homotopy — **(b)**, the one live route. See §6.

### 5.3 Diaconis–Saloff-Coste comparison (1993) — **(b)**, and structurally incapable of dominance

DSC (AAP 1993, Thm 2.1) gives `Ẽ ≤ A·E` with congestion
`A = max_{(z,w)} (1/(π(z)P(z,w))) Σ_{Ẽ(z,w)} |γ_{xy}| π̃(x)P̃(x,y)`, hence
`γ̃ ≤ A·(max_x π(x)/π̃(x))·γ`.

**It requires the same state space.** Verified in the source: DSC AAP §1 — "by
comparison with a second reversible chain **on the same state space**"; the
Dirichlet forms must be quadratic forms on the same `ℝ^X`. BK lives on `L(P)`, the
interchange process on `S_n`.

*Correcting a common belief:* Dyer–Goldberg–Jerrum–Martin (2006) do **not** supply
a different-state-space theorem — they explicitly disclaim it ("Not much is known
about comparison of two chains with very different state spaces"). The general
result is **Aaron Smith, arXiv:1301.7357**, via a one-to-many extension
`f̂(x) = Σ_y P_x[y] f(y)`, giving
`1 − β_i(Q) ≥ (1/(C₁C₃))(1 − β_i(K))` where `C₃` is the DSC congestion **plus**
correction terms for removed states.

**Boundary term:** the extension/detour congestion `C₃`.
**Classification: (b)** — a bounded detour yields `gap_BK ≥ gap_ambient / poly(n)`.

**But note the structural point, applying here and to 5.4 alike:** comparison
methods are **lossy by construction** (`A > 1` except for identical chains),
whereas SD-BK is a **sharp equality**. No comparison argument can certify a
constant of exactly 1. And per §4, the `(b)`-grade conclusion this route would buy
is already available *sharply* from Wilson — so this route is dominated even at
its own target.

### 5.4 Censoring / monotone coupling (Peres–Winkler) — **[blocked, definitively]**

I initially classified this "blocked pending verification". The source check
settles it more sharply:

**Peres–Winkler ("Can Extra Updates Delay Mixing?", *Comm. Math. Phys.* **323**
(2013), 1007–1016) proves no spectral-gap statement at all.** Theorem 1.1
concludes `μ ⪯ ν` and `‖μ−π‖ ≤ ‖ν−π‖` — stochastic domination and **total
variation** for the law at a *fixed time* after a prescribed update sequence. It
is a distance/mixing-time tool. The paper's only gap mentions describe the
conventional method it *replaces*.

Additionally the **monotone-system hypothesis is not removable** (PW: "Other
assumptions, in particular monotonicity of the system, cannot be dispensed with";
Holroyd gives an explicit counterexample without it), and the BK move is an
adjacent transposition, not a monotone single-site update.

**Boundary term:** n/a — wrong output type.
**Classification: blocked** — cannot produce a gap statement even in principle.
*(Correcting the ticket's framing: censoring is not a spectral-gap technique.)*

---

## §6 The tempering / deformation route (geometric lens)

The route the ticket prioritized. Reproduce:
`python3.11 scripts/onethird_mg4a86_sector_leakage_and_tempering.py`.

### 6.1 Setup

`π_β(σ) ∝ exp(−β·V(σ))` on **all** of `S_n`, `V(σ) = #{(x,y) : x <_P y but σ places
y before x}`. Metropolis: pick position `i` uniformly, propose the adjacent swap,
accept w.p. `min(1, e^{−βΔV})`; `ΔV ∈ {−1,0,+1}`.

- `β = 0`: uniform `S_n`, interchange on the path — **Aldous/CLR exact**.
- `β = ∞` restricted to `{V=0}`: **exactly the BK chain**.

*(Normalization caveat, load-bearing: the tempered chain uses step `1/(n−1)`,
**twice** `bk_walk_matrix`'s `1/(2(n−1))`. All comparisons read the BK block
directly off `W_∞` so both are on the same clock. An earlier pass mismatched the
clocks and produced a spurious "discontinuity". Eigenvalues are taken raw — the
`D^{1/2}WD^{-1/2}` symmetrization is numerically destroyed for `β ≳ 40`.)*

### 6.2 Where the deformation degenerates [proven]

> **Proposition.** At `β = ∞`, `L(P)` is **closed** (from an extension, swapping an
> adjacent comparable pair has `ΔV = +1`, rejected; an incomparable pair `ΔV = 0`,
> accepted). So `W_∞ = [[B, 0],[C, T]]` with `B` the BK block and `T` the
> substochastic **collar block** on violating configurations. Hence
> `spec(W_∞) = spec(B) ∪ spec(T)`, and since `W_β` is a polynomial in `x = e^{−β}`,
> **`lim_{β→∞} λ₂(β) = max(λ₂^BK, ρ(T))`.** ∎

| poset | `λ₂(β=20)` | `λ₂(β=80)` | `λ₂^BK` (matched clock) | `ρ(T)` collar | limit governed by |
|---|---|---|---|---|---|
| N-poset (2+2) | 0.872677996 | 0.872677996 | 0.804737854 | **0.872677996** | **collar** |
| chain2+anti2 | 0.872677996 | 0.872677996 | 0.804737854 | **0.872677996** | **collar** |
| V + isolated | 0.804737854 | 0.804737854 | **0.804737854** | 0.785224771 | BK |
| `A₂ ⊕ A₂` | 0.666688041 | 0.666667989 | 0.333333333 | **0.666666678** | **collar** |

**The geometric reading the ticket asked for.** The deformation is *continuous* in
`β`: `π_β` concentrates smoothly onto `L(P)` and `λ₂(β)` converges. What fails is
that **the limit is the wrong object in 3 of 4 constrained cases** — the
rate-limiting mode at large `β` lives in the **collar** of near-feasible
configurations, not in `L(P)`. The collar's mass vanishes like `e^{−β}` but its
**drainage time stays `Θ(1)`**: mass → 0 does not imply timescale → 0.

So *"where does the deformation's geometry degenerate?"* — **not** at the
constraint boundary in the algebraic sense the ticket anticipated, but in the
**collar**, and the degeneration is a **mass-vs-timescale decoupling**. This is
also why a curvature / Bakry–Émery or localization reading describes the
obstruction rather than removing it: the degeneration is precisely a loss of
curvature control in the collar. `A₂ ⊕ A₂` is sharpest — limit `0.6667` vs BK
`0.3333`, a **factor-2 loss in `λ`**, on an ordinal sum.

### 6.3 What tempering gives, and why it is superseded [proven]

  `gap_temper(∞) = min( gap_BK , 1 − ρ(T) ) ≤ gap_BK`.

> **Corollary.** `gap_BK(P) ≥ gap_temper(β=∞)`. Any lower bound on the tempered
> chain's gap lower-bounds the BK gap — and the tempered chain is what a
> Woodard–Schmidler `β`-ladder attacks, starting from `β=0` where CLR is exact.

**Boundary term, named exactly:** `ρ(T)`, the collar spectral radius. The ladder is
lossless **iff `ρ(T) ≤ λ₂^BK`** ("the collar drains faster than BK mixes") — a
**checkable condition strictly weaker than dominance**: classification **(b)**. It
involves only gaps; no `λ_std` anywhere.

*The relevant machinery, stated correctly:* Woodard–Schmidler–Huber (*AAP* **19**
(2009) 617–640) Cor. 3.1 gives, for simulated tempering,
`Gap(P_st) ≥ [γ(A)^{J+3} δ(A)³ / (2^{14}(N+1)^5 J³)] · Gap(T̄₀) · min_{k,j} Gap(T_k|_{A_j})`,
where the overlap is the **normalized ratio**
`δ(A) = min_{|k−l|=1, j} ∫_{A_j} min{π_k,π_l} dλ / π_k[A_j]`
and a second quantity `γ(A) = min_j Π_k min{1, π_{k−1}[A_j]/π_k[A_j]}` appears
alongside it. The constants are severe.

**Why this is superseded.** Wilson (§4) already gives
`gap_BK ≥ (1−cos(π/n))/(n−1)`, **sharply and universally**. The tempering ladder
would at best reproduce that, lossily, through `δ(A)³` and `γ(A)^{J+3}`. So
tempering is a *coherent* route to BK gap lower bounds and a **superseded** one.

And it is not a route to standard dominance at all: `λ_std` never enters the
argument at any step.

### 6.4 Dominance is not preserved along the homotopy [proven]

The excess `λ₂(β) − λ_std(β)` **changes sign** along the path (`A₂ ⊕ A₂`):

| `β` | 0 | 0.5 | 1.0 | 1.5 | **2.0** | 3.0 | 5.0 | ∞ |
|---|---|---|---|---|---|---|---|---|
| `λ₂(β)` | 0.8047 | 0.8316 | 0.8300 | 0.8150 | 0.7950 | 0.7553 | 0.7031 | 0.3333 |
| `λ_std(β)` | 0.0000 | 0.3352 | 0.5899 | 0.7548 | 0.8547 | 0.9486 | 0.9932 | 1.0000 |
| **excess** | **+0.805** | +0.496 | +0.240 | +0.060 | **−0.060** | −0.193 | −0.290 | **−0.667** |

`λ₂(β)` is also **non-monotone** in `β`. Two consequences:

- **No monotone-in-`β` comparison can hold** — the quantity dominance asserts to be
  zero is positive at one end and negative at the other.
- Dominance is **not a homotopy invariant**. Any "it holds at `β=0`, transport it
  to `β=∞`" argument is refuted: at `β=0` the excess is `+0.805`, i.e. dominance
  **fails at the starting point too**.

The zero crossing near `β ≈ 1.7` is the accidental intersection of two unrelated
curves, not a structure to exploit.

---

## §7 The live target: SD-quant, measured

Given §2, an intermediate target aimed at `λ_std`-dominance is aimed at a false
statement. The ticket's candidate list is therefore retargeted:

| Candidate (ticket's list) | Verdict |
|---|---|
| Finite-`β` soft-constraint SD-BK | **Rejected** — §6.4: excess is `+0.805` at `β=0` and changes sign; no `β` where it holds. |
| Curvature/geometry of the gap along the path | **Delivered as an obstruction** (§6.2), not a tool: the collar decoupling *is* a curvature degeneration. |
| Bounded Hamming distance from an ordinal sum | **Rejected as stated** — §2.3: dominance fails *at* ordinal sums, so the base case of any perturbation argument is already false. |
| Bounded-width / series-parallel | Not attempted; no reason the static/dynamic mismatch respects width. |
| Tempering → BK gap lower bound (my §6.3 `T★`) | **Coherent but superseded** by Wilson (§4), sharply. |

**What is left, and it is the right target:** `SD-quant(c)` (§3.2) — well-posed
without sector invariance, untouched by anything above, and the actual content of
the programme's need. It had never been measured.

### 7.1 Measurement

`c(P) := max over the BK λ₂-eigenspace of ‖P_U f‖²/‖f‖²` (max over the eigenspace
is the most favorable reading, and matters because `λ₂` is frequently degenerate).
Reproduce: `python3.11 scripts/onethird_mg4a86_sdquant_overlap.py`.

| poset | `\|L(P)\|` | `dim U` | ratio | `c(P)` |
|---|---|---|---|---|
| antichain-4 *(control: `c` must be 1)* | 24 | 10 | 0.417 | **1.000000** |
| antichain-5 *(control)* | 120 | 17 | 0.142 | **1.000000** |
| antichain-6 *(control)* | 720 | 26 | 0.036 | **1.000000** |
| 3 chains of 2 (`n=6`) | 90 | 20 | 0.222 | 1.000000 |
| N-poset + 2 isolated (`n=6`) | 180 | 22 | 0.122 | 1.000000 |
| chain3 + antichain3 (`n=6`) | 120 | 20 | 0.167 | 1.000000 |
| `A₃ ⊕ A₃` | 36 | — | — | 1.000000 |

Exhaustive plus an `n=6` random sample:

| set | posets | min `c` | median `c` |
|---|---|---|---|
| `n=4` all | 195 | 0.988718 | 1.000000 |
| `n=5` all | 4111 | 0.988718 | 1.000000 |
| `n=5` informative stratum (`dim U ≤ |L(P)|/2`) | 841 | 0.990257 | 1.000000 |
| `n=6` random sample, informative stratum | 2043 | **0.978898** | 1.000000 |

### 7.2 Calibration — this is essential and I nearly reported it wrong

`c ≈ 1` is **vacuous** when `dim U ≈ |L(P)|`, since then `P_U ≈ I`. At `n=4` the
median ratio `dim U / |L(P)|` is **1.0** — `U` fills the whole space — so the
`n=4` row carries **no information**. Only the stratified rows do. At `n=5` the
median ratio is 0.70 with 841 posets at `≤ 0.5`; the `n=6` sample and the antichain
controls (ratios down to **0.036**) are the genuinely informative measurements,
and there `c` is still `≥ 0.979`.

### 7.3 Honest reading, and where this is predicted to break

**Supported at `n ≤ 6`:** the slowest BK mode has essentially full overlap with the
one-particle span, even when that span is 3.6% of the space.

**But this is weak evidence for the programme, for a specific reason.** The repo's
own analysis (`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:282-290`) reports
`n=7` **off-regime refuters** (`enum-n7-#600`, `#3`, `#20`) whose slow mode is
explicitly **degree-2** — a lone frozen pair — with `λ₂^BK ≈ 0.98` against
`λ_std ≈ 0.77`. A genuinely degree-2 slow mode has **small** overlap with `U`, i.e.
`c ≈ 0` there. **My sweep does not reach those posets**, so §7.1 does *not*
contradict them, and it must not be read as evidence that SD-quant is universal.

**The decisive next experiment**, cheap and well-specified: compute `c(P)` on
`enum-n7-#600/#3/#20` from the `mg-8b64` data. Predicted outcome `c ≈ 0`, which
would show SD-quant is *conditional* on the all-pairs-frozen regime — matching the
repo's `L1b ⟺ "all-pairs-frozen ⇒ standard dominance"`. I did not run it: it needs
the specific `n=7` posets from that dataset, `|L(P)|` up to 5040, and the ticket
bars large enumerations. **Flagged as the single highest-value follow-on.**

---

## §8 Honest verdict

**On the ticket's question** ("does any route yield a real partial result, or does
the boundary term reduce to full standard dominance in every case?"): **neither.**
The boundary terms do *not* reduce to full standard dominance — in the tempering
case the term is exactly `ρ(T)`, strictly weaker and checkable. But no route
yields a partial result *about dominance*, because SD-BK is **false** and `λ_std`
is not in the range of any comparison method.

**On the octopus framing.** The ticket's stated crux is correct as a statement
about the octopus (§5.0), and I found no way around it. But it is **not the
binding obstruction**. Two independent reasons: (i) the conclusion the octopus
would buy is already available, sharply, from Wilson 2004 (§4) — and it does not
give dominance; (ii) the failure is visible before any octopus, since `L(P)`
carries no `S_n` action, hence no invariant standard sector (§3.2), hence no
reason for `λ_std` to be in the BK spectrum — confirmed by its absence in
4306/4306 cases.

**Corrections owed to the repo** (both load-bearing elsewhere):
1. `OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md` — the "0/132" GREEN is
   **SD-Cayley** evidence and should not be read as support for any BK-chain
   statement (§1.1). ✅ **DISCHARGED — landed at the destination by `mg-e2a0`**, together with
   the independent sampling-frame correction (`mg-55f2` / `mg-65f5` §1.5): that document now
   carries a scope-correction banner at its head and in-place strikes at its executive-verdict
   row, its *Kill-shot 2* heading, its *"standard dominance is universal"* sentence, and its
   Data-appendix `0 / 132` row. (Named by section: the banner shifted every line below it by +59,
   so the old refs `:20`/`:103`/`:249`/`:286` now read `:63`/`:146`/`:303`/`:345`.) This
   correction had been owed since `mg-4a86` and had never reached the document a reader is sent
   to.
2. `OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:273-275` — "`λ_std ≤ λ₂^BK` (the
   standard sector is a subspace)" — the justification is invalid, and the
   inequality itself fails on **every** ordinal sum (§2.3), i.e. throughout the
   programme's regime of interest. ✅ **DISCHARGED — struck at the destination by
   `mg-d1be`**, which also **refuted the "and exactly there" rescue**: the set equality is a
   small-`n` coincidence, false from `n = 7` on and broken wholesale at `n = 8` (§2.4). The
   §5 conclusion it supported survives on stronger ground (incomparability, not a wrong-way
   inequality).

**Also worth recording:** the programme should know that
`gap_BK ≥ (1−cos(π/n))/(n−1)` universally (Wilson 2004, §4). It is sharp, free,
and I did not find it cited anywhere in the repo.

**What to pursue:**
- **SD-quant** (§7) — the well-posed version of the need, `c ≥ 0.979` at `n ≤ 6`,
  with a specified decisive test at `n=7` (§7.3).
- **The ordinal-sum product formula** (§2.3) — an exact, reusable theorem.

**What not to pursue:** lifting the octopus/CLR to `L(P)` *for the purpose of
standard dominance*. The lift is exact on the antichain and dominance fails there
hardest; a sharp universal lift already exists and gives nothing. The two are
unrelated.

---

## §9 Literature, verified

Statements below were checked against primary sources rather than paraphrased.

- **Aldous's conjecture / CLR.** P. Caputo, T. M. Liggett, T. Richthammer, "Proof
  of Aldous' spectral gap conjecture", *J. Amer. Math. Soc.* **23** (2010),
  831–851, [doi:10.1090/S0894-0347-10-00659-4](https://doi.org/10.1090/S0894-0347-10-00659-4),
  arXiv:0906.1238. Thm 1.2: for all weighted graphs with connected skeleton,
  `λ₁^IP(G) = λ₁^RW(G)`. *(The arXiv title says "A recursive proof…"; cite the JAMS
  form.)* Companion: A. B. Dieker, *SIAM J. Discrete Math.* **24** (2010), 191–206.
- **Octopus inequality.** CLR Thm 2.3 (probabilistic form); equivalent group-algebra
  form in F. Cesi, *Comm. Algebra* **44** (2016), 279–302, Thm 4.2
  (arXiv:1310.6156). Hypotheses: `c_{xy} ≥ 0` only. Quoted in §5.0.
- **Madras–Randall.** *Ann. Appl. Probab.* **12** (2002), 581–606, Thm 1.1:
  `Gap(P) ≥ Θ^{-2} Gap(P_H) min_i Gap(P_{[A_i]})`. **Overlapping-cover theorem;
  vacuous on a disjoint partition.** Proved via Caracciolo–Pelissetto–Sokal (1992,
  unpublished, MR Appendix A). For disjoint partitions: **Martin–Randall**
  (*CPC* **15** (2006), 411–448) or **JSTV**.
- **JSTV.** Jerrum, Son, Tetali, Vigoda, *Ann. Appl. Probab.* **14** (2004),
  1741–1765, Thm 1: `λ ≥ min{λ̄/3, λ̄λ_min/(3γ+λ̄)}` with escape parameter `γ`;
  adds a log-Sobolev version and inductive-decomposition bounds.
- **Diaconis–Saloff-Coste.** *Ann. Appl. Probab.* **3** (1993), 696–730, Thm 2.1
  (congestion `A`, eq. 2.4) — **same state space required**. The groups paper is
  *Ann. Probab.* **21** (1993), 2131–2156. Different state spaces: **A. Smith,
  arXiv:1301.7357**; Dyer–Goldberg–Jerrum–Martin (*Probab. Surveys* **3** (2006),
  89–111) explicitly *disclaim* such a theorem.
- **Peres–Winkler censoring.** "Can Extra Updates Delay Mixing?", *Comm. Math.
  Phys.* **323** (2013), no. 3, **1007–1016**, arXiv:1112.0603. Thm 1.1 —
  stochastic domination + total variation, **monotone systems only**, and **no
  spectral-gap conclusion**. *(A citation of "325, 907–917" is in circulation and
  is wrong.)* Counterexample without monotonicity: Holroyd, arXiv:1101.4690.
- **Tempering.** Woodard–Schmidler–Huber, *Ann. Appl. Probab.* **19** (2009),
  617–640, Thm 3.1 / Cor. 3.1, with `δ(A)` a **normalized ratio** and a second
  quantity `γ(A)`; torpid-mixing companion *EJP* **14** (2009), 780–804.
  Madras–Zheng, *Random Structures Algorithms* **22** (2003), 66–97.
- **The linear-extension chain.** Karzanov–Khachiyan, *Order* **8** (1991), 7–15
  (`O(n^6 log n)`); Bubley–Dyer, *Discrete Math.* **201** (1999), 81–88
  (`O(n³ log n)` — **for the parabolic chain `M_F`, not the uniform KK chain**);
  **Wilson**, *Ann. Appl. Probab.* **14** (2004), 274–325, §6 + Table 1 + Prop. 3
  (arXiv:math/0102193) — `Θ(n³ log n)` mixing for KK on general posets, and the
  **universal gap bound of §4**. Survey: Chan–Pak, arXiv:2311.02743, §12.2.
  *Different* chains do better (Ayyer–Schilling–Thiéry random-to-random,
  arXiv:1412.7488) but are not adjacent-transposition chains.

---

## §10 Reproduction

| Script | Produces | Certificate |
|---|---|---|
| `onethird_mg4a86_standard_dominance_target_audit.py` | §2.1, §2.2, §2.4 (`n = 4,5` table only), §2.5 | `data/onethird-mg4a86-standard-dominance-target-audit.json` |
| `onethird_mgd1be_reverse_cheeger_ineq_audit.py` | §2.4 **refutation** (`n ≤ 6` up to iso; width ≤ 3 at `n = 7,8`) + both exact certificates | `data/onethird-mgd1be-reverse-cheeger-ineq-audit.json` |
| `onethird_mg4a86_sector_leakage_and_tempering.py` | §3.2, §6.2, §6.4 | `data/onethird-mg4a86-sector-leakage-tempering.json` |
| `onethird_mg4a86_ordinal_sum_theorem_check.py` | §2.3 | `data/onethird-mg4a86-ordinal-sum-check.json` |
| `onethird_mg4a86_sdquant_overlap.py` | §7 | `data/onethird-mg4a86-sdquant-overlap.json` |

All run under `python3.11` (the repo's numpy environment). Of the `mg-4a86` scripts, none
carries a large enumeration: largest sweep is 4111 labeled posets at `n=5`; `n!`-sized
tempered chains capped at `n ≤ 5`; the `n=6` work is a capped random sample plus named
structured cases. **The `mg-d1be` audit is the exception** — 7789 isomorphism classes at
`n = 8` in exact rational arithmetic. It is already exact and should **not** be re-run to
confirm §2.4; read its certificate instead.

**Built-in controls** (each catches a specific failure mode):
- antichain `λ₂^BK` vs. the closed-form single-particle value — validates the BK
  matrix against CLR (residual `≤ 5.2e-15`);
- antichain leakage ≈ 0 and `dim U = (n−1)²+1` — validates the sector projector.
  **This control caught a real bug:** an initial QR-based rank filter reported
  `dim U = 11` and leakage `0.218` on antichain-4, where both must be `10` and `0`;
  fixed with an SVD rank test;
- **enumeration completeness**: the sweep finds `195` (`n=4`) and `4111` (`n=5`)
  posets. Labeled partial orders number `219` and `4231` (OEIS A001035), and the
  excluded `|L(P)|<2` cases are exactly the total orders (`24`, `120`):
  `219−24 = 195` ✓, `4231−120 = 4111` ✓ — provably exhaustive, not a sample;
- ordinal sums: `|L(P)| = Π|L(P_i)|` and the predicted gap formula (§2.3);
- Wilson's universal bound reproduced exactly, 0/4306 violations (§4) — an
  independent check of both the BK construction and the literature statement;
- SD-quant control: `c = 1` on antichains, where the slowest mode provably *is* the
  single-particle mode;
- tempered chain at `β=0` reproduces the uniform-`S_n` interchange gap; antichain
  rows are `β`-independent (`V ≡ 0`).

**Known numerical limits.** The `D^{1/2}WD^{-1/2}` symmetrization of the tempered
chain is unusable for `β ≳ 40` (conditioning `~e^{βΔV}`); §6 uses raw eigenvalues.
`n=6` results are a capped sample, not exhaustive. Nothing here reaches `n=7`.

**Repo cross-references:** `step1.tex:20-26`, `step8.tex:21-25,85-112`;
`scripts/onethird_mgb0a6_spectral_killshot_probe.py:19-25,263-296,459-475`;
`docs/OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md:20,103-119,286`;
`docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:269-315`;
`docs/OneThird-L1b-ExpectedRank-Certificate.md:53-56`.
