# Standard Dominance: the comparison / deformation route

**Work item:** mg-4a86
**Deliverable:** map the comparison/decomposition/tempering route from Aldous
single-particle dominance (ambient `S_n` interchange) to the constrained BK chain
on `L(P)`; identify the best intermediate target and attempt it.

---

## §0 Executive verdict

**The ticket's target statement is false, and I can prove it.** The route was
scoped as "lift Aldous dominance to get `λ₂^BK = λ_std`". That conclusion fails
on **0 / 195** posets at `n=4` and **0 / 4111** at `n=5` — it holds nowhere — and
it fails structurally, not marginally, on the class the programme treats as
extremal (ordinal sums). This is not a near-miss to be repaired by a better
comparison argument.

**The reason is a category mismatch, and it is more fundamental than the octopus
obstruction the ticket anticipated.** The ticket's framing ("the octopus's
rerouting passes through non-extensions, so the operator inequality does not
restrict") is a correct statement about the octopus, but it is not the binding
constraint. The binding constraint is:

> `λ₂^BK` is a **dynamical** functional (the gap of a generator). `λ_std` is a
> **static** functional of the stationary measure alone (the top eigenvalue of
> the symmetrized element-position marginal matrix). `λ_std` is not the spectral
> gap of any chain in the comparison family. Every technique in the toolkit —
> decomposition, tempering, Diaconis–Saloff-Coste, censoring — produces
> inequalities between *Dirichlet forms*. None of them can have `λ_std` as an
> endpoint, because `λ_std` is not one.

The sharpest evidence is the **antichain**, and it points the opposite way from
the ticket's intuition. On the antichain the constraint is empty, `L(P) = S_n`,
the BK chain *is* the interchange process on the path, and the Aldous/CLR lift is
**exact** (verified to `5e-15`). That is precisely where `λ_std`-dominance fails
**maximally**: `λ_std = 0` while `λ₂^BK = 1 − (1−cos(π/n))/(n−1) → 1`. The lift
working perfectly and dominance failing completely are the *same* case.

**What is salvageable.** The tempering/deformation route — the one the ticket
prioritized — does yield a real, correctly-directed result, just not dominance:

> **`gap_BK(P) ≥ gap_temper(β=∞) = min( gap_BK , gap_collar )`**, with the
> constraint-boundary term identified exactly as `ρ(T)`, the spectral radius of
> the substochastic **collar block** (the violating configurations). This is
> classification **(b)**: strictly weaker than dominance, and *checkable*.

**Honest bottom line.** No route yields standard dominance, and the reduction is
not "boundary term ⟹ full dominance" (the ticket's anticipated dead-end) — it is
worse and cleaner than that: dominance is **not in the image** of any comparison
method. Per the ticket's own success criterion ("a clean, rigorous 'here is the
reduction and here is exactly why it is not weaker' is a fully successful
outcome"), that is the deliverable. Two genuine positive theorems fall out along
the way (§2.3, §5.3).

### Claim ledger

| # | Claim | Tag |
|---|---|---|
| C1 | `λ_std(antichain_n) = 0` while `λ₂^BK → 1`; dominance excess → 1 | **[proven]** (hand proof §2.1 + exact numerics) |
| C2 | `λ₂^BK = λ_std` holds for 0/195 (`n=4`) and 0/4111 (`n=5`) posets | **[proven]** (exhaustive) |
| C3 | The repo's asserted inequality `λ_std ≤ λ₂^BK` fails **exactly on the ordinal sums**, and holds elsewhere | **[proven]** (exact set equality at `n=4,5`; §2.4) |
| C4 | Ordinal sums: exact BK product formula; `λ_std = 1`; dominance fails on the whole class | **[proven]** (hand proof §2.3 + 9/9 numeric) |
| C5 | The one-particle sector `U` is invariant on ambient `S_n` but **not** on `L(P)`; leakage measured | **[proven]** (§3.2) |
| C6 | `lim_{β→∞} λ₂(β) = max(λ₂^BK, ρ(T))` (block-triangularity) | **[proven]** (§5.2) |
| C7 | The collar term dominates in 3/4 constrained test cases, so the tempering limit ≠ BK | **[proven]** (numerics §5.2) |
| C8 | No comparison technique can prove dominance (category mismatch) | **[heuristic]** — rigorous for each of the 4 techniques individually (§4), but "every conceivable comparison method" is not a formal quantifier |
| C9 | Tempering yields `gap_BK ≥ gap_temper(∞)`, a usable gap lower bound | **[proven]** (§5.3) |

---

## §1 Three inequivalent statements called "standard dominance"

The repo and the ticket use one name for three different things. Disentangling
them is most of the work; once separated, the verdicts are immediate.

Fix a finite poset `P` on `[n]`, `L(P)` its linear extensions.

- **Transport / standard block** (repo convention, `onethird_mgb0a6_spectral_killshot_probe.py:263-296`):
  `(T_P)_{x,a} = Pr_{σ~Unif L(P)}[σ(a) = x]`, `S_P = (T_P + T_Pᵀ)/2`,
  `λ_std(P) =` top eigenvalue of `S_P` on `H = 𝟙^⊥`.
  **This depends only on the measure `Unif L(P)`, not on any dynamics.**
- **BK chain** (`step1.tex:20-26`, `step8.tex:21-25`): lazy walk on `L(P)`, step
  `1/(2(n−1))` per adjacent incomparable position. `λ₂^BK` its second eigenvalue.
- **Cayley walk** (`onethird_mgb0a6_spectral_killshot_probe.py:459-475`): walk on
  **all of `S_n`** with generating measure `η_P = (μ_P + μ_P^∨)/2`, `μ_P` uniform
  on `L(P)` *viewed as a set of permutations*.

The three statements:

| Name | Statement | Status |
|---|---|---|
| **SD-Cayley** | `λ₂(Cayley walk) = λ_std` | Empirically supported, **0/132** (`mgb0a6`). Coherent and nontrivial. |
| **SD-BK** | `λ₂^BK = λ_std` | **FALSE** — 0/4306 (§2). This is the ticket's target. |
| **SD-quant** | the slowest BK mode has an `Ω(1)` component in the standard sector | Coherent, conditional, open. The programme's actual need (`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:269-270`). |

### 1.1 The "0/132" evidence does not support the ticket's target

The ticket asserts SD-BK is "empirically airtight (0/132 counterexamples)". **The
0/132 figure is SD-Cayley evidence, and does not transfer.** The Cayley walk lives
on `S_n` with generating set `L(P)`; the BK chain lives on `L(P)` with
adjacent-transposition generators. Different state space, different generators.

SD-Cayley is also *near-automatic* in a way SD-BK is not: by Schur's lemma
`ρ_std(η_P) = S_P` exactly, so `λ_std` is *guaranteed* to sit in the Cayley
spectrum, and SD-Cayley only asserts that no other irrep out-eigenvalues it. On
`L(P)` there is **no group action at all**, so no irrep decomposition, so no
sector in which `λ_std` is guaranteed to appear (§3.2). The repo already records
this at `mgb0a6`'s own scope correction
(`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:290`: "**Standard dominance is not
universal**").

### 1.2 A second citation error, inherited

`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:273-275` asserts

> "But `λ_std ≤ λ₂^{BK}` (the standard sector is a subspace)"

**This is false as stated, but in a precisely characterizable way** (C3, §2.4):
it holds on every poset that is *not* an ordinal sum, and fails on *every* ordinal
sum. The stated justification is nonetheless invalid — it presupposes that the
standard sector embeds in `L²(L(P))` as an invariant subspace so that `λ_std` is a
Rayleigh restriction, which it does not (§3.2). So the inequality is *true off the
ordinal sums for some other reason*, not for the reason given.

This matters for the programme in a specific way: the inequality is used to argue
that Theorem E "bounds the gap in the wrong direction". That argument survives on
non-ordinal-sums — but the near-ordinal-sum regime is exactly where the programme
operates, and that is exactly where the inequality reverses.

---

## §2 SD-BK is false

Reproduce: `python3.11 scripts/onethird_mg4a86_standard_dominance_target_audit.py`
(certificate: `data/onethird-mg4a86-standard-dominance-target-audit.json`).

### 2.1 The antichain [proven]

Let `P = A_n`, the `n`-element antichain, so `L(P) = S_n`.

**`λ_std(A_n) = 0`.** By symmetry `Pr[σ(a) = x] = 1/n` for every `x,a`, so
`T_P = J/n`, hence `S_P = J/n`. On `H = 𝟙^⊥`, `J` acts as `0`. ∎

**`λ₂^BK(A_n) = 1 − (1−cos(π/n))/(n−1)`.** The BK chain on `L(A_n) = S_n` is
exactly the interchange process on the path `P_n` with rate `1/(2(n−1))` per edge.
By Aldous / Caputo–Liggett–Richthammer its gap equals the single-particle gap.
*(The disproof does not actually need CLR: the `≥` direction is elementary. Take
`f(σ) = g(σ^{-1}(x₀))` for a fixed element `x₀` and `g` the path's Fiedler
vector; `f` is a one-particle observable whose BK Dirichlet form is exactly the
single-particle one, so `λ₂^BK ≥ 1 − (1−cos(π/n))/(n−1)` by Rayleigh. That alone
contradicts `λ₂^BK = λ_std = 0` for `n ≥ 3`.)*

**Verified** (residual vs. the closed form `≤ 5.2e-15`):

| `n` | `λ₂^BK` | single-particle | residual | `λ_std` | excess `λ₂^BK − λ_std` |
|---|---|---|---|---|---|
| 3 | 0.750000000 | 0.750000000 | 0.0 | 0 | **0.750** |
| 4 | 0.902368927 | 0.902368927 | 5.6e-16 | 0 | **0.902** |
| 5 | 0.952254249 | 0.952254249 | 1.1e-15 | 0 | **0.952** |
| 6 | 0.973205081 | 0.973205081 | 2.1e-15 | 0 | **0.973** |
| 7 | 0.983494811 | 0.983494811 | 5.2e-15 | 0 | **0.983** |

**Read this carefully — it inverts the ticket's premise.** The antichain is the
case where the constraint is *empty* and the Aldous lift is *exact*. The ticket
expected the obstruction to live where the constraint bites. It does not: the
obstruction is maximal where the constraint vanishes. So the obstruction is not
about the constraint at all.

### 2.2 Exhaustive: dominance holds nowhere [proven]

All labeled posets on `[n]` with `|L(P)| ≥ 2`:

| `n` | tested | `λ₂^BK = λ_std` holds | fails | `λ_std > λ₂^BK` (refutes the §1.2 inequality) | worst excess |
|---|---|---|---|---|---|
| 4 | 195 | **0** | 195 | 33 | 0.902368927 |
| 5 | 4111 | **0** | 4111 | 550 | 0.952254249 |

Not one instance in 4306. And the failure is two-sided: 583 posets violate even
the weak inequality — characterized exactly in §2.4.

### 2.3 Ordinal sums: an exact theorem, and an infinite counterexample family [proven]

This is the structurally important case: the programme's own characterization is
`λ_std = 1` **iff** `P` is an ordinal sum
(`OneThird-L1b-ExpectedRank-Certificate.md:53-56`), so ordinal sums are the
extremal class the whole near-ordinal-sum programme is organized around.

> **Theorem (ordinal-sum product formula).** Let `P = P₁ ⊕ ⋯ ⊕ P_k` be an ordinal
> sum, `|P_i| = n_i`, `n = Σ n_i`. Then
>
> 1. `L(P) = L(P₁) × ⋯ × L(P_k)` by concatenation, and the BK graph on `L(P)` is
>    the **Cartesian product** of the BK graphs on the `L(P_i)`.
> 2. In the repo normalization,
>    `gap_BK(P) = min_i gap_BK(P_i) · (n_i − 1)/(n − 1)`.
> 3. `λ_std(P) = 1`, i.e. the transport gap is `0`.
>
> **Corollary.** For every ordinal sum with at least one block that is neither a
> singleton nor a chain, `gap_BK(P) > 0 = 1 − λ_std(P)`. **SD-BK fails on the
> entire class of nontrivial ordinal sums**, and `λ_std > λ₂^BK` there, refuting
> §1.2's inequality on an infinite family.

*Proof of (1).* In an ordinal sum, two elements are incomparable only if they lie
in the same block. An adjacent pair of a linear extension is therefore swappable
only if both members are in one block, so every BK move is internal to a block
and blocks never interleave. ∎ *(2) follows since the generator is then a direct
sum, and a chain's gap is linear in its step rate. (3) is the cited
characterization, independently reconfirmed numerically below.*

**Verified**, 9/9 families, gap formula exact to `1e-9`
(`scripts/onethird_mg4a86_ordinal_sum_theorem_check.py`):

| ordinal sum | `\|L(P)\|` | gap actual | gap predicted | `λ_std` | SD-BK? |
|---|---|---|---|---|---|
| `A₃ ⊕ A₃` | 36 | 0.100000000 | 0.100000000 | 1.000000 | NO |
| `A₂ ⊕ A₂` | 4 | 0.333333333 | 0.333333333 | 1.000000 | NO |
| `A₂ ⊕ A₃` | 12 | 0.125000000 | 0.125000000 | 1.000000 | NO |
| `A₂ ⊕ A₂ ⊕ A₂` | 8 | 0.200000000 | 0.200000000 | 1.000000 | NO |
| `A₄ ⊕ C₁` | 24 | 0.073223305 | 0.073223305 | 1.000000 | NO |
| `A₂ ⊕ C₂ ⊕ A₂` | 4 | 0.200000000 | 0.200000000 | 1.000000 | NO |
| `V₃ ⊕ A₂` | 4 | 0.250000000 | 0.250000000 | 1.000000 | NO |

(`|L(P)| = Π|L(P_i)|` confirmed on all; full table in the JSON certificate.)

Note the direction: on ordinal sums `λ_std = 1 > λ₂^BK`, whereas on antichains
`λ_std = 0 < λ₂^BK`. The two extremal classes of the programme straddle the
claimed equality from opposite sides. Any putative proof of SD-BK would have to
be false at both ends.

### 2.4 Exactly where the weak inequality fails [proven]

The 583 violations of §2.2 are not scattered. Comparing the violation set
`{P : λ_std > λ₂^BK}` against the set `{P : λ_std = 1}` (= the ordinal sums, by
the programme's own characterization):

| `n` | posets | `λ_std > λ₂^BK` | `λ_std = 1` | **sets equal?** | symmetric difference |
|---|---|---|---|---|---|
| 4 | 195 | 33 | 33 | **YES** | 0 |
| 5 | 4111 | 550 | 550 | **YES** | 0 |

> **Proposition (exact characterization).** For every labeled poset on `n ≤ 5`
> with `|L(P)| ≥ 2`:
> `λ_std(P) > λ₂^BK(P)` **⟺** `λ_std(P) = 1` **⟺** `P` is an ordinal sum.
> Equivalently: **`λ_std ≤ λ₂^BK` holds precisely off the ordinal sums.**

The `⟸` direction is the §2.3 Corollary and is **proven for all `n`** (ordinal sums
have `λ_std = 1` and `λ₂^BK < 1` whenever `|L(P)| ≥ 2`). The `⟹` direction is
**verified exhaustively at `n = 4,5`** and is [heuristic] beyond that.

This is a sharper and fairer correction than "the inequality is false": it is true
on the generic poset and fails on a thin, exactly-identified set — which happens
to be the set the near-ordinal-sum programme is built around.

---

## §3 Why: the mismatch is static-vs-dynamic, not constrained-vs-ambient

### 3.1 Different objects, different scaling [proven]

Aldous/CLR controls the **single-particle random walk on the graph** — a
functional of the *generator*. `λ_std` is the top eigenvalue of the symmetrized
*stationary marginal* matrix — a functional of the *measure*. Nothing forces them
to agree, and on the antichain they do not even scale alike in `n`:

- transport gap `1 − λ_std(A_n) = 1` — **`Θ(1)`**;
- BK gap `1 − λ₂^BK(A_n) = (1−cos(π/n))/(n−1) ≍ π²/(2n³)` — **`Θ(n^{-3})`**.

No constant rescaling reconciles a `Θ(1)` quantity with a `Θ(n^{-3})` one. The
two "one-particle" objects are genuinely different, and the ticket's phrase
"one-particle / standard-representation object" silently identifies them.

### 3.2 There is no standard sector on `L(P)` [proven]

On `S_n`, the span `U = span{ σ ↦ 𝟙[σ(a)=x] }` of one-particle observables is
**invariant** under the interchange process: a move permutes the position index
`a`, mapping `U` into `U`. That invariance is exactly what makes "the gap lives in
the standard sector" well-posed, and it is what Schur/CLR exploit.

On `L(P)` the move at position `i` fires only when `σ(i), σ(i+1)` are
incomparable — the action on the position index is **`σ`-dependent** — so `U`
need not be invariant. Measure the leakage

  `leak(P) := ‖ (I − P_U) W P_U ‖_op`,

which is `0` iff `U` is BK-invariant. This is the constraint-boundary term of
*any* sector-based argument, made concrete:

| poset | `\|L(P)\|` | `dim U` | leakage |
|---|---|---|---|
| antichain-4 *(control: ambient `S_n`)* | 24 | 10 | **9.5e-16** |
| antichain-5 *(control: ambient `S_n`)* | 120 | 17 | **1.5e-15** |
| N-poset (2+2) | 6 | 5 | **1.44e-01** |
| chain2+anti2 | 12 | 8 | **1.44e-01** |
| V + isolated | 8 | 6 | **1.00e-01** |
| `A₂ ⊕ A₂` | 4 | 3 | 2.5e-16 *(degenerate: `dim U = 3`, `\|L(P)\| = 4`)* |

The controls confirm the implementation: on the antichain, leakage is machine-zero
and `dim U = (n−1)²+1` exactly (10 at `n=4`, 17 at `n=5`, 5 at `n=3`), matching
the ambient theory. On genuinely constrained posets the leakage is **`Θ(0.1)`**,
not small.

**Consequence.** On `L(P)` there is no invariant standard sector, hence no
guarantee that `λ_std` appears in the BK spectrum *at all* — which is why SD-BK
can (and does) fail in both directions. The correct formulation of the
programme's need is therefore an **overlap** statement (SD-quant), not a
sector-decomposition statement:

  `SD-quant(c)`: the top nontrivial BK eigenfunction `f` satisfies `‖P_U f‖² ≥ c‖f‖²`.

This is well-posed without invariance, and it is what a transfer to the transport
quotient actually requires.

---

## §4 The four techniques: boundary terms and classification

Classification per the ticket: **(a)** still full standard dominance;
**(b)** strictly weaker / checkable; **(c)** tractable on a sub-class.

### 4.1 State-space decomposition (Madras–Randall 2002; Jerrum–Son–Tetali–Vigoda 2004) — **[blocked]**

Slice `S_n` by violation count: `Ω_k = {σ : V(σ) = k}`, `Ω_0 = L(P)`. The
restriction of the ambient chain to `Ω_0` is exactly BK.

**The inequality points the wrong way.** Madras–Randall lower-bounds the gap of
the **full** chain by (restriction gaps) × (projection gap):

  `gap(full) ≳ min_k gap(restriction_k) · gap(projection)`.

Here the *hard* chain is the restriction (BK) and the *easy* chain is the full one
(ambient, where Aldous applies). Decomposition is designed to bound a hard chain
by easy pieces; we need the exact converse — bound a hard **piece** by the easy
**whole** — which decomposition does not provide. Knowing `gap(full)` places no
lower bound on any `gap(restriction_k)`; a single slice can be arbitrarily slow
while the whole mixes fine.

**Boundary term:** the projection chain on violation-levels `{0,1,…,K}`.
**Classification: blocked** — not (a), (b) or (c); the technique is structurally
inapplicable in this direction. *(This is a cleaner "no" than the ticket
anticipated: the term does not collapse to dominance, the method simply does not
point this way.)*

### 4.2 Simulated tempering / soft-constraint homotopy — **(b), and the one live route.** See §5.

### 4.3 Diaconis–Saloff-Coste comparison (1993) — **(b), but structurally incapable of dominance**

DSC compares two chains via canonical paths, with congestion constant `A`, giving
`gap₁ ≥ gap₂ / A`. Two obstructions here:

1. **State spaces differ.** BK lives on `L(P)`, the interchange process on `S_n`.
   DSC in its basic form requires a common state space; the extension needs a map
   `S_n → L(P)` (e.g. "sort into an extension") and the congestion picks up the
   fiber sizes.
2. **Detour cost.** Ambient paths between two linear extensions may leave `L(P)`;
   they must be rerouted inside `L(P)`. The boundary term is the **detour
   congestion** — the ratio of BK-graph distance to Cayley distance on `L(P)`.

**Boundary term:** fiber/detour congestion `A`.
**Classification: (b)** — a bounded detour yields `gap_BK ≥ gap_ambient / poly(n)`,
a genuine and weaker conclusion.

**But note the structural point, which applies to this technique and 4.4 alike:**
comparison methods are **lossy by construction** (`A > 1` always, except for
identical chains), whereas SD-BK is a *sharp equality*. **No comparison argument
can ever certify a constant of exactly 1.** Even if every congestion estimate were
optimal, the output is an inequality with a loss, not dominance. Combined with §2
(the equality is false anyway), this route cannot reach the stated target — though
its `(b)` output is worth having on its own terms.

### 4.4 Censoring / monotone coupling (Peres–Winkler) — **[blocked]**

Censoring requires a **monotone** chain with respect to a partial order on the
state space, together with a monotone (e.g. FKG / positively associated) measure;
the conclusion is that censoring updates cannot speed up convergence.

`L(P)` does carry natural order structure (the ticket's framing via maximal flags
of the distributive lattice `J(P)`; `L(P)` under inversion-containment). However
the BK move is an **adjacent transposition, not a monotone single-site update** —
it is not a monotone spin-system update in the sense the censoring inequality
requires. I could not establish the monotonicity hypothesis for the BK chain, and
I am **not** asserting it fails.

**Boundary term:** the monotonicity hypothesis itself.
**Classification: blocked pending verification** — plausibly **(c)** on a subclass
where `L(P)` with weak order is a distributive lattice and the down-up walk
formulation makes the updates genuinely monotone. Flagged as **not attempted in
depth**; this is the least-explored of the four and the honest place to say so.

---

## §5 The tempering / deformation route (geometric lens)

The route the ticket prioritized, and the only one that produces a
correctly-directed result. Reproduce:
`python3.11 scripts/onethird_mg4a86_sector_leakage_and_tempering.py`.

### 5.1 Setup

Gibbs measure on **all** of `S_n`:
  `π_β(σ) ∝ exp(−β·V(σ))`, `V(σ) = #{(x,y) : x <_P y but σ places y before x}`.

Metropolis: pick a position `i ∈ {1,…,n−1}` uniformly, propose the adjacent swap,
accept w.p. `min(1, e^{−β ΔV})`. Note `ΔV ∈ {−1,0,+1}` for an adjacent swap (only
the swapped pair's relation changes), so the deformation is clean.

- `β = 0`: uniform on `S_n`, the interchange process on the path — **Aldous/CLR
  applies exactly**.
- `β = ∞` restricted to `{V = 0}`: **exactly the BK chain**.

*(Normalization caveat, load-bearing: the tempered chain uses step `1/(n−1)`,
**twice** the repo's `bk_walk_matrix` rate `1/(2(n−1))`. All comparisons below
read the BK block directly off `W_∞` so both are on the same clock. An earlier
pass of this analysis mismatched the clocks and produced a spurious
"discontinuity"; it is corrected here. Eigenvalues are taken raw — the
`D^{1/2}WD^{-1/2}` symmetrization is numerically destroyed for `β ≳ 40`.)*

### 5.2 The geometry: where the deformation degenerates [proven]

> **Proposition.** At `β = ∞`, `L(P)` is **closed** (from a linear extension, any
> swap of an adjacent comparable pair has `ΔV = +1` and is rejected; a swap of an
> incomparable pair has `ΔV = 0` and is accepted). Hence `W_∞` is block
> triangular,
> `W_∞ = [[B, 0], [C, T]]`, with `B` the BK block on `L(P)` and `T` the
> substochastic **collar block** on the violating configurations. Therefore
> `spec(W_∞) = spec(B) ∪ spec(T)` and, since `W_β` is a polynomial in `x = e^{−β}`
> (so eigenvalues are continuous in `x` at `x=0`),
>
>   **`lim_{β→∞} λ₂(β) = max( λ₂^BK , ρ(T) )`.** ∎

**Verified**, with clean convergence (no discontinuity — the earlier report of one
was the clock mismatch):

| poset | `λ₂(β=20)` | `λ₂(β=80)` | `λ₂^BK` (matched clock) | `ρ(T)` collar | limit governed by |
|---|---|---|---|---|---|
| N-poset (2+2) | 0.872677996 | 0.872677996 | 0.804737854 | **0.872677996** | **collar** |
| chain2+anti2 | 0.872677996 | 0.872677996 | 0.804737854 | **0.872677996** | **collar** |
| V + isolated | 0.804737854 | 0.804737854 | **0.804737854** | 0.785224771 | BK |
| `A₂ ⊕ A₂` | 0.666688041 | 0.666667989 | 0.333333333 | **0.666666678** | **collar** |

**The geometric reading the ticket asked for.** The deformation is *continuous* in
`β` — the measure `π_β` concentrates smoothly onto `L(P)`, and `λ₂(β)` converges.
What fails is that **the limit is the wrong object in 3 of 4 constrained cases**:
the rate-limiting mode of the tempered chain at large `β` lives in the **collar**
of near-feasible configurations, not in `L(P)`. The collar's `π_β`-mass vanishes
like `e^{−β}`, but its **drainage time stays `Θ(1)`**. Mass → 0 does not imply
timescale → 0.

So: *"where does the deformation's geometry degenerate?"* — **not** at the
constraint boundary in the algebraic sense the ticket anticipated (the octopus's
non-restriction), but in the **collar**, and the degeneration is a
mass-vs-timescale decoupling. The `A₂ ⊕ A₂` case is the sharpest: the tempering
limit `0.6667` versus the BK value `0.3333` is a **factor-2 loss in `λ`**, on an
ordinal sum — exactly the class the programme cares about.

### 5.3 What tempering *does* give [proven]

The Proposition has a useful corollary, in the **right** direction:

  `gap_temper(∞) = 1 − max(λ₂^BK, ρ(T)) = min( gap_BK , 1 − ρ(T) ) ≤ gap_BK`.

> **Corollary (C9).** `gap_BK(P) ≥ gap_temper(β=∞)`. Hence **any lower bound on
> the tempered chain's gap is a lower bound on the BK gap** — and the tempered
> chain is precisely the object a Woodard–Schmidler `β`-ladder decomposition can
> attack, starting from `β = 0` where Aldous/CLR gives the answer exactly.

**Boundary term, named exactly:** `ρ(T)`, the collar spectral radius. The ladder
recovers the BK gap **iff `ρ(T) ≤ λ₂^BK`** — "the collar drains faster than BK
mixes". That is a **checkable condition strictly weaker than dominance**:
classification **(b)**, as promised in §4.2. It is a statement purely about
`gap`s — no `λ_std` anywhere.

**And that last observation is the whole verdict.** The tempering route is a live
route to **BK gap lower bounds**. It is *not* a route to standard dominance,
because `λ_std` never enters the argument at any step — there is nowhere for it to
appear. Which brings us to §6.

### 5.4 Dominance is not preserved along the homotopy [proven]

Independent of the endpoint analysis: the excess `λ₂(β) − λ_std(β)` **changes
sign** along the deformation path (`A₂ ⊕ A₂`):

| `β` | 0 | 0.5 | 1.0 | 1.5 | **2.0** | 3.0 | 5.0 | ∞ |
|---|---|---|---|---|---|---|---|---|
| `λ₂(β)` | 0.8047 | 0.8316 | 0.8300 | 0.8150 | 0.7950 | 0.7553 | 0.7031 | 0.3333 |
| `λ_std(β)` | 0.0000 | 0.3352 | 0.5899 | 0.7548 | 0.8547 | 0.9486 | 0.9932 | 1.0000 |
| **excess** | **+0.805** | +0.496 | +0.240 | +0.060 | **−0.060** | −0.193 | −0.290 | **−0.667** |

The excess starts at `+0.805`, crosses zero near `β ≈ 1.7`, and ends at `−0.667`.
Also note `λ₂(β)` is **non-monotone** in `β` (it rises then falls). Two
consequences:

- **No monotone-in-`β` comparison can hold** — the quantity dominance asserts to
  be zero is positive at one end and negative at the other.
- Dominance is **not a homotopy invariant** of this deformation. Any argument of
  the form "it holds at `β=0`, transport it to `β=∞`" is refuted: at `β=0` the
  excess is `+0.805`, i.e. dominance *fails at the starting point too*.

The zero crossing at `β ≈ 1.7` is not a structure to exploit; it is the accidental
intersection of two unrelated curves.

---

## §6 Most promising intermediate target, and the attempt

The ticket asked for the single most promising intermediate target, weighted
toward tempering, with a genuine attempt. Given §2, the honest answer must first
retarget: **`λ_std`-dominance is not available at any strength**, so an
intermediate target aimed at it is aimed at a false statement.

### 6.1 Targets considered and why they were rejected

| Candidate (ticket's list) | Verdict |
|---|---|
| Finite-`β` soft-constraint version of SD-BK | **Rejected** — §5.4: the excess is `+0.805` at `β=0` and changes sign; there is no `β` at which a soft SD-BK holds robustly. |
| Geometric/curvature behavior of the gap along the path | **Partially delivered** (§5.2) — but Bakry–Émery/localization needs a log-concave or curvature-bounded structure; the collar decoupling (mass→0, timescale `Θ(1)`) is exactly a curvature *degeneration*, so a curvature reading describes the obstruction rather than removing it. |
| Bounded Hamming distance from an ordinal sum | **Rejected as stated** — §2.3 shows dominance fails *at* ordinal sums (`λ_std=1 > λ₂^BK`), so the base case of any perturbation argument is already false. |
| Bounded-width / series-parallel posets | Not attempted; no reason to expect the static/dynamic mismatch to respect width. |

### 6.2 The target I selected and attempted: the collar criterion

> **T★.** `gap_BK(P) ≥ gap_temper(∞) = min(gap_BK, 1 − ρ(T))`, with the transfer
> from `β=0` (Aldous, exact) to `β=∞` losing exactly the collar term `ρ(T)`.

**Attempt outcome: the reduction is proven (§5.2–5.3, C6/C9), the collar bound is
not.** What I have:

- the identity `lim_{β→∞} λ₂(β) = max(λ₂^BK, ρ(T))` — **proven** by
  block-triangularity;
- the correct direction `gap_BK ≥ gap_temper(∞)` — **proven**;
- the criterion "`ρ(T) ≤ λ₂^BK` ⟺ the ladder is lossless" — **proven**, and
  strictly weaker than dominance;
- **numerically, `ρ(T) > λ₂^BK` in 3 of 4 constrained cases** — so the criterion
  *fails* on the tested posets, and the ladder is lossy exactly there.

What is **missing** and is the honest blocker: a bound on `ρ(T)` in terms of `P`.
The collar block is substochastic with a `σ`-dependent structure; I have no
handle on its spectral radius beyond computing it. Bounding `ρ(T)` for a family
of posets is the concrete next question, and it is a self-contained one — it
involves no `λ_std`, no representation theory, and no octopus.

**Calibration.** T★ is a real reduction with a real gap in it. It is **not** a
proof of anything about standard dominance, and I am not claiming it is a
partial proof of dominance — §6.3 explains why no such thing exists.

### 6.3 Why no intermediate target reaches dominance [heuristic, but rigorous per-technique]

Collecting §4 and §5:

> Every technique in the comparison-lift toolkit produces inequalities between
> **Dirichlet forms / spectral gaps of Markov chains**. Standard dominance
> equates a dynamical quantity (`λ₂^BK`) to a **static functional of the measure**
> (`λ_std`), which is not the gap of any chain in the family. There is no step in
> any of these arguments at which `λ_std` can enter.

Per-technique this is rigorous (§4.1 wrong direction; §4.3 lossy-by-construction
and different state spaces; §4.4 hypothesis unverified; §5 no `λ_std` term
anywhere). As a claim about *every conceivable* comparison method it is a
**[heuristic]** generalization, not a theorem — I flag it as such rather than
dress it up.

The one place `λ_std` legitimately appears in a spectral identity is
`ρ_std(η_P) = S_P` for the **Cayley** walk (§1.1) — which requires the `S_n`
action, i.e. requires *not* being constrained to `L(P)`. That is the real content
of the obstruction, and it is upstream of the octopus.

---

## §7 Honest verdict

**On the ticket's question** ("does any route yield a real partial result, or does
the boundary term reduce to full standard dominance in every case?"): **neither.**
The boundary terms do *not* reduce to full standard dominance — they are genuinely
weaker and, in the tempering case, exactly identifiable (`ρ(T)`). But no route
yields a partial result *about dominance*, because dominance as stated (SD-BK) is
**false**, and no comparison method has `λ_std` in its range.

**On the octopus framing.** The ticket's stated crux — "the octopus's rerouting
passes through non-extensions, so the operator inequality does not restrict" — is
correct as far as it goes, and I did not find a way around it. But it is **not the
binding obstruction**, and a programme organized around defeating it would be
solving the wrong problem. The binding obstruction is visible before any octopus:
`L(P)` carries no `S_n` action, hence no invariant standard sector (§3.2), hence
no reason for `λ_std` to be in the BK spectrum — confirmed by its absence in
4306/4306 cases.

**Corrections owed to the repo** (both load-bearing elsewhere):
1. `OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md` — the "0/132" GREEN is
   **SD-Cayley** evidence; it should not be read as support for any BK-chain
   statement. (`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:311-315` already
   corrects the scope; this doc explains *why* the two are inequivalent.)
2. `OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:273-275` — "`λ_std ≤ λ₂^BK` (the
   standard sector is a subspace)" is **false**; 583 counterexamples at `n≤5` plus
   the infinite ordinal-sum family (§2.3). The premise (an invariant standard
   sector in `L²(L(P))`) does not hold.

**What survives and is worth pursuing:**
- **SD-quant** (§3.2) — the overlap formulation `‖P_U f‖² ≥ c‖f‖²` — is the
  well-posed version of what the programme needs, and is untouched by anything
  here. It is *not* implied by, and does not imply, SD-BK.
- **T★ / the collar criterion** (§6.2) — a live, self-contained question about
  `ρ(T)` with a proven reduction attached, yielding BK gap lower bounds.
- **The ordinal-sum product formula** (§2.3) — an exact, reusable theorem.

**What should not be pursued:** lifting the octopus/CLR to `L(P)` *for the purpose
of standard dominance*. The lift is exact on the antichain and dominance fails
there hardest; the two are unrelated.

---

## §8 Reproduction and cross-references

| Script | Produces | Certificate |
|---|---|---|
| `scripts/onethird_mg4a86_standard_dominance_target_audit.py` | §2.1 antichain table, §2.2 exhaustive `n=4,5` | `data/onethird-mg4a86-standard-dominance-target-audit.json` |
| `scripts/onethird_mg4a86_sector_leakage_and_tempering.py` | §3.2 leakage, §5.2 endpoint, §5.4 sign change | `data/onethird-mg4a86-sector-leakage-tempering.json` |
| `scripts/onethird_mg4a86_ordinal_sum_theorem_check.py` | §2.3 ordinal-sum theorem check | `data/onethird-mg4a86-ordinal-sum-check.json` |

All run under `python3.11` (the repo's numpy environment). No large enumerations:
the largest sweep is 4111 labeled posets at `n=5`; state spaces are capped at
`n ≤ 5` for the `n!`-sized tempered chains.

**Built-in controls** (each catches a specific failure mode):
- antichain `λ₂^BK` vs. the closed-form single-particle value — validates the BK
  matrix construction against CLR (residual `≤ 5.2e-15`);
- antichain leakage ≈ 0 and `dim U = (n−1)²+1` — validates the sector projector
  *(this control caught a real bug: an initial QR-based rank filter reported
  `dim U = 11` and leakage `0.218` on antichain-4, where both must be `10` and
  `0`; fixed with an SVD rank test)*;
- **enumeration completeness**: the sweep finds `195` posets at `n=4` and `4111`
  at `n=5`. Labeled partial orders number `219` and `4231` (OEIS A001035), and
  the excluded `|L(P)|<2` cases are exactly the total orders (`4! = 24`,
  `5! = 120`): `219−24 = 195` ✓, `4231−120 = 4111` ✓. The enumeration is
  provably exhaustive, not a sample;
- ordinal sums: `|L(P)| = Π|L(P_i)|` and the predicted gap formula — validates
  §2.3;
- tempered chain at `β=0` reproduces the uniform-`S_n` interchange gap, and
  antichain rows are `β`-independent (`V ≡ 0`).

**Repo cross-references:**
`step1.tex:20-26`, `step8.tex:21-25,85-112` (BK definitions);
`scripts/onethird_mgb0a6_spectral_killshot_probe.py:19-25,263-296,459-475`
(`λ_std`, Cayley walk);
`docs/OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md:20,103-119,286` (SD-Cayley, 0/132);
`docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:269-315` (SD-quant, the false
inequality, the scope correction);
`docs/OneThird-L1b-ExpectedRank-Certificate.md:53-56` (`λ_std = 1` ⟺ ordinal sum).
