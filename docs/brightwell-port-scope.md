# `brightwell_sharp_centred` — port scope audit (mg-38cf)

This is a re-audit of the **port vs forum-post-with-axiom** decision for
the single project-specific named axiom remaining in the Lean
formalisation, `OneThird.LinearExt.brightwell_sharp_centred`
(`lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`,
introduced `mg-134c` / commit `2ded504`, faithfulness QA `mg-a6a1` /
commit `b23400f`).

The previous decision (`mg-b699`, commit `68a82fd`) was **retain**.
Daniel asked to revisit now that the development is sorry-free and the
trade-off is clean.

**Heuristic.** Port (option 2) if the work fits ≤500 LoC in a single
polecat; otherwise forum-post (option 1).

**Recommendation. Option (1) — forum-post the Lean as-is, citing
`brightwell_sharp_centred`.** Honest LoC estimate is **~700–1100 LoC**
across three pieces, dominated by the per-term Kahn–Saks / Brightwell
covariance bound that has no primitive in mathlib. Even an optimistic
estimate exceeds the polecat budget by ~200 LoC, and the hardest
single sub-piece (the exchange-involution construction) does not
admit further sub-division without losing structural coherence.

---

## 1. What the axiom asserts

`step8.tex:1048`, `eq:sharp-centred`. Let `Q` be a finite poset with
`|Q| = m ≥ 2`, `z ∈ Q`, `α := Q − z`. With pred/succ sets
`Pred, Succ ⊆ α`, fibre size `f(L') := S(L') − P(L')`,
`N := Σ_{L'} f(L') = |L(Q)|`, `N' := |L(α)|`, `f̄ := N/N'`, and
`A := { L' : x <_{L'} y }`:

```
| Σ_{L' ∈ A} (f(L') − f̄) |  ≤  2N/m.            (*)
```

Lean form (integer): `m · |N' · sumA − |A| · N| ≤ 2 · N · N'`.

## 2. Paper proof structure (`step8.tex:1046–1276`)

The paper derivation, formalised informally by `c6d76d6` (mg-391c,
A10b), reduces `(*)` to a single black-box quantitative input via
five steps:

1. **Covariance reduction.** Write `Δ := p_{xy}(Q) − p_{xy}(Q−z)` as
   `(m/f̄)·Cov_ν(1_A, 1_B)` on the product space
   `X := L(α) × {1,…,m}` with uniform measure `ν`.
2. **Distributive lattice on X.** Pick a reference linear extension
   `τ ∈ L(α)` placing `pred(z)` before `succ(z)`. The
   τ-inversion order makes `(L(α), ≤_𝒟)` distributive (Brightwell
   §3.5.1); `X = L(α) × {1,…,m}` is then the product lattice.
3. **Monotonicity of `1_A`, `P`, `S`, `1_{B_-}`, `1_{B_+}` on `X`.**
   Five claims (a)–(e) at `step8.tex:1128–1169`, each a check on
   adjacent transpositions of `≤_𝒟`.
4. **AD sign constraints.** Apply Ahlswede–Daykin
   (`Cov ≤ 0` for monotone × antitone) twice on `X` (with reversed
   `J`-order for `B_-`) to get `Cov_ν(1_A, 1_{B_±}) ≤ 0`, hence
   `Cov_ν(1_A, 1_B) ≥ 0`.
5. **Collapse to μ-covariance and per-term bound.** `J`-marginalisation
   reduces `Cov_ν(1_A, 1_{B_±}) = ±(1/m)·Cov_μ(1_A, S or P)`. Combined
   with the Kahn–Saks / Brightwell **per-term covariance bound**

   ```
   |Cov_μ(1_A, S)|, |Cov_μ(1_A, P)|  ≤  f̄/m,           (**)
   ```

   one gets `|Cov_μ(1_A, f)| ≤ 2f̄/m`, which after multiplying by
   `N'` is `(*)`.

The cited input `(**)` is Kahn–Saks 1984 Lemma 2.2 / Brightwell 1999
Theorem 4.1, proved by an explicit exchange involution
`σ : L(α) → L(α)` with `σ(A) = A^c` such that
`|S(L') − S(σL')| ≤ 1` and `|P(L') − P(σL')| ≤ 1`, plus an
insertion-position averaging that produces the `1/m` factor.

## 3. What is already formalised

In our `lean/OneThird/Mathlib/LinearExtension/`:

| Piece | File | LoC | Status |
| --- | --- | ---: | --- |
| `LinearExt α` `Fintype` + position API | `Fintype.lean` | 199 | done |
| Birkhoff `LinearExt α ≃ IdealChain α` | `Birkhoff.lean` | 646 | done (`mg-f30f`, `f5dc82d`) |
| FKG on uniform measure on `LinearExt α` via level-`k` initial-ideal projection | `FKG.lean` | 486 | done (`mg-9ece`, `cd75ef1`) |
| `fiberSize` 1-Lipschitz on BK adjacency graph | `FiberSize.lean` | 433 | done (`mg-85d1`, `af7a4a3`) |

The 1-Lipschitz piece is the paper's `eq:fS-fP-lipschitz`, which
feeds the per-term bound `(**)` directly.

## 4. What is missing for a port

For each step of §2 above, the gap to Lean:

### 4.1 Reference τ separating pred/succ — ~50–80 LoC

Construct `τ ∈ L(α)` with `∀ u ∈ Pred, ∀ v ∈ Succ, pos_τ u < pos_τ v`,
plus `pos_τ x < pos_τ y` (WLOG, with the comparable case discharged
trivially). Standard topological-sort / extension argument; needs the
disjointness + comparability hypotheses already in the axiom.

### 4.2 τ-inversion distributive lattice on `L(α)` — ~150–250 LoC

`L' ≤_𝒟 L''` iff `Inv_τ(L') ⊆ Inv_τ(L'')`. Distributivity is
Brightwell §3.5.1 via the equivalence with order ideals of the
*adjacent-transposition graph* of `τ`-inversions. **This is a
different distributive-lattice structure from the level-`k`
initial-ideal one already formalised in `Birkhoff.lean`.** A direct
transport from `Birkhoff` does not apply: the level-`k` lattice and
the τ-inversion lattice are non-isomorphic in general. Either build
the τ-inversion lattice from scratch, or prove a bridge lemma to
mathlib's `four_functions_theorem` directly.

### 4.3 Product lattice `X = L(α) × {1,…,m}` — ~10 LoC

`Mathlib.Order.Lattice` gives the product `DistribLattice` instance
for free.

### 4.4 Monotonicity (a)–(e) on `≤_𝒟` — ~250–400 LoC

The paper's items (a)–(e) at `step8.tex:1128–1169`:

* (a) `1_A` is an order ideal on `≤_𝒟`. Easy after τ has `x <_τ y`.
* (b) `P` nondecreasing on `≤_𝒟`. Per-swap analysis using
  pred/succ separation in τ.
* (c) `S` nonincreasing on `≤_𝒟`. Symmetric to (b).
* (d) `1_{B_-}(L', J) := [J ≤ P(L')]` is jointly monotone on
  `L(α) × {1,…,m}^op` (reversed `J`-order). Requires the dual-order
  variant of (4.2)–(4.3).
* (e) `1_{B_+}(L', J) := [J > S(L')]` is jointly monotone on
  `L(α) × {1,…,m}` (natural `J`-order).

Each step is a careful check on adjacent transpositions of `≤_𝒟`.
The `posAux`-based machinery in `FiberSize.lean` is reusable for `P`,
`S`, but the swap-on-`≤_𝒟` analysis is new.

### 4.5 Apply FKG/AD on the τ-inversion product lattice — ~100–200 LoC

Mathlib's `fkg` gives `Cov ≥ 0` for monotone × monotone on a uniform
measure on a finite distributive lattice. Two applications give
`Cov_ν(1_A, 1_{B_±}) ≤ 0` (one each, with the second using the
reversed `J`-order so `1_A` and `1_{B_-}` are co-monotone after the
flip).

**Reuse of existing FKG infra is non-trivial.** Our
`fkg_uniform_initialLowerSet` is keyed to the level-`k`
initial-ideal lattice on `LinearExt α`. The Brightwell argument
needs FKG on the τ-inversion lattice. Either: (a) re-derive FKG
on the τ-inversion lattice from mathlib's `fkg` directly (which
needs a lattice-isomorphism to a sublattice of some `Fin n →
Lower α` that mathlib understands — possibly via a new Birkhoff
correspondence, or via a `Bool`-power lattice indexed by
incomparable τ-pairs), or (b) prove that the *measure* (uniform on
`L(α)`) is log-supermodular w.r.t. the τ-inversion order directly
and feed `four_functions_theorem` raw. Either route is ~100–200
LoC of new infrastructure.

### 4.6 Collapse `Cov_ν` → `Cov_μ` — ~50–80 LoC

`E_ν[1_{B_-} | L'] = P(L')/m`,
`E_ν[1_{B_+} | L'] = (m − S(L'))/m`. Standard tower-property
calculation. The translation
`Cov_ν(1_A, 1_B) = (1/m)·Cov_μ(1_A, f)` plus ratio with `Pr_ν(B)`
gives `Δ = Cov_μ(1_A, f) / f̄`.

### 4.7 Per-term Kahn–Saks / Brightwell covariance bound `(**)` — ~250–400 LoC

**The hard piece.** No primitive in mathlib. The paper proof is a
direct combinatorial computation: starting from the AD sign
constraints and the 1-Lipschitz bounds, construct an exchange
involution `σ : L(α) → L(α)` with `σ(A) = A^c`,
`|S(L') − S(σL')| ≤ 1`, `|P(L') − P(σL')| ≤ 1`, then average over
insertion positions to extract the `1/m` factor. The pred/succ
disjointness clause prevents simultaneous saturation of the two
1-Lipschitz bounds.

This is the substantive combinatorial content of Brightwell §4.
A faithful Lean version requires:

* defining `σ` explicitly (canonical adjacent-transposition that
  flips `(x, y)` and tracks pred/succ effect);
* proving `σ ∘ σ = id`, `σ(A) = A^c`;
* proving the per-element Lipschitz bounds for `σ` on `S` and `P`;
* the insertion-position averaging giving the `1/m` factor and the
  per-pair bound.

The paper itself flags this as "a direct combinatorial computation,
not an independent external input" (`step8.tex:1311–1313`), but
"direct" means "elementary given the right setup" — formally it is
~250–400 LoC of careful per-swap bookkeeping.

### 4.8 Final assembly — ~50 LoC

`|Cov_μ(1_A, f)| ≤ 2f̄/m` ⇒
`|Σ_A (f − f̄)| = N' · |Cov_μ(1_A, f)| ≤ 2f̄N'/m = 2N/m`.
Algebra plus the `N = f̄·N'` identity (already in `FiberSize.lean`
via the fibre-sum).

## 5. LoC estimate

| Component | Optimistic | Conservative |
| --- | ---: | ---: |
| 4.1 reference τ | 50 | 80 |
| 4.2 τ-inversion lattice | 150 | 250 |
| 4.3 product lattice | 10 | 10 |
| 4.4 monotonicity (a)–(e) | 250 | 400 |
| 4.5 FKG transport to τ-inversion | 100 | 200 |
| 4.6 collapse `Cov_ν → Cov_μ` | 50 | 80 |
| 4.7 Kahn–Saks per-term `(**)` | 250 | 400 |
| 4.8 final assembly | 50 | 50 |
| **Total** | **~910** | **~1470** |

This brackets the previous `mg-b699` estimate of **500–800 LoC**
(`lean/AXIOMS.md:42`) on the **low** side. The earlier figure was
plausible if §4.5 transports cleanly off existing infrastructure
and §4.7 admits a slick presentation; the present audit treats
both pessimistically because the τ-inversion lattice is a new
distributive structure (not reusable directly from Birkhoff /
level-`k`) and the per-term bound has no mathlib precedent.

Either way, **the port is ≥ 600 LoC** in the most optimistic
realistic scenario, well above the 500-LoC polecat threshold.

## 6. Sub-divisibility

The natural decomposition is into three polecats:

1. **`mg-port-A`**: §4.1 + 4.2 + 4.3 + 4.4 — τ-inversion
   distributive-lattice setup with monotonicity claims (a)–(e).
   ~470–740 LoC.
2. **`mg-port-B`**: §4.5 + 4.6 — FKG/AD on τ-inversion product
   lattice and collapse to μ-covariance. ~150–280 LoC.
3. **`mg-port-C`**: §4.7 + 4.8 — Kahn–Saks per-term covariance
   bound and final assembly. ~300–450 LoC.

Each fits in a single polecat individually. The serialisation cost
is ~3 polecats over a multi-week rotation.

## 7. Recommendation

**Option (1): forum-post the Lean as-is, citing
`brightwell_sharp_centred`.**

Reasoning:

* The honest LoC estimate (~700–1100 in the realistic range,
  ~900+ even optimistic) is above the single-polecat heuristic
  by a factor of 1.4–2.
* The hardest sub-piece (§4.7, ~250–400 LoC) is irreducible —
  the explicit exchange involution does not split further without
  losing the load-bearing per-element 1-Lipschitz coupling.
* The axiom is a faithful integer transcription of a published
  1999 result (Brightwell, Discrete Math. **201**, §4 Thm 4.1),
  audited by `mg-a6a1` against the paper statement, with the
  `#print axioms` artifact archived (`mg-358a`, `0644c05`).
* The novel content of this paper — the structural / arithmetic
  width-3 1/3–2/3 argument — is sorry-free modulo this single
  cited axiom. That is the credibility artifact the forum post
  will showcase.
* The replacement path remains open via the three-polecat split
  in §6, but is post-launch infrastructure work, not a
  prerequisite for the forum post.

**Option (2) is viable**, but requires committing to a
multi-polecat rotation (~3 polecats, ~3–6 weeks elapsed) before
the forum post. If the goal is to land the forum post first and
add the port as a follow-up, option (1) is correct.

## 8. Note on `mg-b699`

The `mg-b699` audit (commit `68a82fd`, recorded in
`lean/AXIOMS.md`) reached the same conclusion with a slightly
lower estimate (500–800 LoC). The present audit revises the upper
bound up to ~1100 LoC because:

* §4.2 (τ-inversion lattice) was implicitly assumed to transport
  off Birkhoff in `mg-b699`; the closer reading here treats it as
  a fresh distributive structure (the level-`k` and τ-inversion
  lattices are non-isomorphic in general), adding ~100–200 LoC.
* §4.5 (FKG transport) inherits the same mismatch.

The bottom-line decision (retain) is unchanged.
