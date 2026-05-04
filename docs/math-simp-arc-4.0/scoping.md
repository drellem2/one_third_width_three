# Math-simp arc 4.0 — spectral / character-theoretic strategy on the BK walk (test fixed-point-mode-rigidity hypothesis)

> **EXPLORATORY ONLY — NOT a live program.**
>
> This file is the deliverable for `mg-0bc8` (arc 4.0 kickoff,
> 2026-05-05, branch `math-simp-arc-4.0`). It is the answer to
> Daniel's in-session directive (~2026-05-05T00:00Z) sketching
> a fresh spectral / character-theoretic strategy on the BK
> walk and asking it "should at least be investigated".
>
> The deliverable is a **strategy-level audit**, not a
> commission to execute. Months from now, treat this doc the
> same way arc 2.0 / arc 3.0 scoping should be treated: a
> record of evaluation under specific assumptions, **not a
> backlog**. Verdict at §7.
>
> The headline `OneThird.width3_one_third_two_thirds` retains
> `hC3 : Step8.Case3Witness` (intentionally) under
> pm-onethird's option (δ) park (2026-04-27). This arc neither
> overturns nor confirms that retention; it asks whether
> Daniel's spectral / character-theoretic strategy would close
> `hC3` where existing strategies cannot. The verdict is
> **RED** at Step 2 by direct computation on the K=2 N-poset.

---

## 0. Provenance and outcome class

* **Filed under** `mg-0bc8` (arc 4.0 scoping, polecat `p0bc8`).
* **Sibling arcs (closed).**
  * `mg-3e53` — arc 1.0 scoping. 4 candidates (A/B/C/D);
    recommended A.
  * `mg-3d9d` — arc 1.0 A1 RED-fallback (perturbation slack).
  * `mg-805c` — arc 1.0 B1 ship.
  * `mg-80ab` — arc 2.0 scoping. Zero GREEN of 4 framings.
  * `mg-65e1` — arc 3.0 scoping. Zero GREEN of 8 ε-close
    definitions × 12 strategy alternatives. §2.6 D6 spectral
    defect verdict: tautological in the wrong direction.
  * `mg-b666` — Track 1 cardinality obstruction (F1).
  * `mg-cda8` — F1/F2/F3 synthesis-as-deliverable
    (`docs/why-hC3-is-structural.md`).
* **Input table.** `notes/bk-walk-irrep-eigenvalue-bounds.md`
  (mg-7e24, landed 2026-05-04). Three eigenvalue-mode bounds
  per non-trivial S_n irrep on `L(P) ⊆ S_n`.
* **Outcome class.** Substantive scoping chunk, no parallel
  cleanup. Per `feedback_distinguish_arc_chunk_outcomes`: the
  scoping doc IS the deliverable. Headline / axiom inventory /
  hC3 retention / sorry-count all unchanged by this ticket.

---

## 1. Setup and prior-context audit

### 1.1 The strategy under test (Daniel, 2026-05-05T~00:00Z)

> *use that table to derive from our layered gap case some bad
> spectral behavior on the S_n walk. Then we can hopefully do
> something with that, perhaps show that S_n dynamics match BK*
>
> *The dynamics strategy should focus on:*
> *define G_P = L(P) ⊆ S_n*
> *bound:*
>   *parity imbalance*
>   *fixed-point excess*
>   *2-cycle excess*
> *prove only the fixed-point mode can be large*
> *show large fixed-point mode implies layered rigidity / reducibility*
> *otherwise spectral gap ⇒ balanced pair*

### 1.2 The four-step structure (per ticket mg-0bc8)

1. **Step 1.** For each of the three non-trivial S_n irreps —
   sign `[1^n]`, standard `[n-1, 1]`, two-row `[n-2, 2]` —
   compute the empirical-statistic bound on the corresponding
   eigenvalue mode of the BK walk on `L(P) ⊆ S_n`.
2. **Step 2.** Prove that the parity (sign) bound and the
   2-cycle bound are both `≤ δ < 1/3` on the K=2 obstruction
   family — leaving only the fix-point mode potentially
   large.
3. **Step 3.** Prove that large `E[fix(g)]` implies layered
   rigidity / reducibility (so existing G3-style reductions
   fire).
4. **Step 4.** In the residual case (small fix-point mode),
   all eigenvalue modes are small, hence by Cheeger the BK
   walk has a spectral gap, hence by Theorem E (in tree) a
   balanced pair exists.
5. **(Optional) Step 5.** S_n dynamics match BK — relate the
   BK walk on `L(P)` to a canonical S_n walk so the table's
   bounds transfer rigorously.

### 1.3 The eigenvalue-bound table (Daniel's working note)

Recapitulating
`notes/bk-walk-irrep-eigenvalue-bounds.md` for self-containment:

| irrep `ρ`              | character measures          | empirical statistic on `L(P)`          | eigenvalue bound                                                        |
|------------------------|-----------------------------|-----------------------------------------|--------------------------------------------------------------------------|
| sign `[1^n]`           | parity                      | `Σ(P) = Σ_{g ∈ G_P} (-1)^{sgn(g)}`      | `|λ_sign| = |Σ(P)| / |G_P|`                                              |
| standard `[n-1, 1]`    | `χ(g) = fix(g) − 1`         | `E[fix] = (1/|G_P|) Σ_g fix(g)`         | `|λ_std| ≤ (E[fix] − 1) / (n − 1)`                                       |
| two-row `[n-2, 2]`     | `χ(g) = #2-cycles(g) − 1`   | `E[#2c]`                                | `|λ_{[n-2,2]}| ≤ (E[#2c] − 1) / (n(n−3)/2)`                              |

**Important caveat (mathematical rigor).** These bounds, as
written, are character-theoretic identities for the random
transposition walk on **full S_n**. The BK walk on
`L(P) ⊆ S_n` is **not** the random transposition walk on `S_n`;
its state space is a subset (not subgroup), its transition
edges are restricted to **adjacent transpositions** that
preserve linear-extension membership, and `Aut(P)` is much
smaller than `S_n` (often trivial — see F1). The claim
"|λ_ρ| (on the BK walk) is bounded by the empirical statistic
on `L(P)`" therefore needs a separate derivation. **No such
derivation is in tree, in `notes/bk-walk-irrep-eigenvalue-bounds.md`,
or in cited published literature** that the polecat could
locate. This is a Step 5 / "S_n ↔ BK matching" prerequisite,
not a Step 1 input. See §6 for further discussion.

For the rest of §2–§3 we **grant the bounds at face value**
and ask whether Step 2 holds *as if* the bounds were
rigorous. Even granting that, Step 2 fails on the K=2 N-poset.

### 1.4 What this arc is — and is not

* **Is.** A polecat-scoping evaluation of Daniel's
  spectral / character-theoretic strategy against the K=2
  obstruction family. Verdict per §7.
* **Is not.** A new mathematical attack on `δ_3* ≥ 1/3`.
  Polecats do not have authority for paper-level math (per
  `feedback_audit_bar_for_axioms`); per ticket §Constraints,
  if Steps 2 / 3 require fresh published-literature theorems
  the polecat **stops and escalates**. Step 2 fails on direct
  computation, so the escalation question doesn't fire.

### 1.5 Distinction from arc 3.0 D6 (spectral defect)

Arc 3.0 §2.6 D6 — *spectral defect as ε-close invariant* —
was RED on the grounds that bounding `λ_2(BK(P))` from
**cardinality** data is tautological in the wrong direction
(Cheeger goes eigenvalue → conductance; the proof needs
structure → eigenvalue, which Steps 5–7 already supply
non-trivially).

Daniel's new strategy bounds `λ_2` from **empirical statistics
on `L(P)`** (sign-imbalance, fix-point count, 2-cycle count)
— combinatorial input that is *not* derived from cardinality
alone and *not* the same content as Steps 5–7. The
distinction is real and worth testing. **However, the arc 3.0
D6 critique still bites in a related way**: even if the input
statistics are different, the Step 3 connection ("large
E[fix] ⇒ layered rigidity") risks collapsing into an
invocation of Steps 5–7 in spectral clothing. We flag this
in §4 below.

### 1.6 Required prior-context audit (per ticket)

| File                                                             | Role                                                            | Read |
|------------------------------------------------------------------|-----------------------------------------------------------------|------|
| `notes/bk-walk-irrep-eigenvalue-bounds.md` (mg-7e24)             | Daniel's working table (Step-1 inputs)                          | ✓    |
| `step8.tex` §G1 / Theorem E (`thm:cex-implies-low-expansion`)    | In-tree Cheeger machinery (Step-4 consumer)                     | ✓    |
| `docs/path-c-track-1-status-1.md` §2 (mg-b666)                   | F1 — cardinality obstruction; minimal counterexample            | ✓    |
| `docs/math-simp-arc-3.0/scoping.md` §2.6 (D6)                    | Prior negative spectral-route finding                           | ✓    |
| `docs/why-hC3-is-structural.md` (mg-cda8)                        | F1/F2/F3 unified statement; obstruction-family definition       | ✓    |

In-tree Lean machinery (`MainAssembly.lean`, etc.) is **not
modified** by this arc — latex-first scoping only.

---

## 2. Step 1 — eigenvalue-mode bounds on the K=2 N-poset and siblings

We compute the three empirical statistics and the resulting
eigenvalue bounds on the K=2 N-poset (the canonical
small-K=2 irreducible base case, per
`feedback_n_poset_is_not_ordinal_sum`) and several siblings
spanning the obstruction-family neighbourhood.

### 2.1 The K=2 N-poset

**Definition.** `α = {x_1, x_2, y_1, y_2}` with cover
relations `x_1 < y_1` and `x_2 < y_2` (no other comparabilities).
Bands: `band(x_i) = 1`, `band(y_i) = 2`. So `K = 2`,
`w = 0`, `|β| = 2` (two strict cover pairs).

**Linear extensions** (fixing reference `L_0 = (x_1, x_2, y_1, y_2)`,
labels `1 = x_1, 2 = x_2, 3 = y_1, 4 = y_2`; identify each LE
`L` with the permutation `σ(i) = posₗ(label_i) ∈ S_4`):

| #   | LE                            | `σ` (cycle notation) | sign | `fix(σ)` | `#2-cyc(σ)` |
|-----|-------------------------------|----------------------|------|----------|-------------|
| L_1 | `(x_1, x_2, y_1, y_2)`        | `e`                  | +1   | 4        | 0           |
| L_2 | `(x_1, x_2, y_2, y_1)`        | `(3 4)`              | −1   | 2        | 1           |
| L_3 | `(x_1, y_1, x_2, y_2)`        | `(2 3)`              | −1   | 2        | 1           |
| L_4 | `(x_2, x_1, y_1, y_2)`        | `(1 2)`              | −1   | 2        | 1           |
| L_5 | `(x_2, x_1, y_2, y_1)`        | `(1 2)(3 4)`         | +1   | 0        | 2           |
| L_6 | `(x_2, y_2, x_1, y_1)`        | `(1 3 4 2)`          | −1   | 0        | 0           |

`|G_P| = |L(P)| = 6`.

### 2.2 Sign-imbalance bound (irrep `[1^n]`)

```
Σ(P)  =  +1 − 1 − 1 − 1 + 1 − 1  =  −2.
```

```
|λ_sign|  =  |Σ(P)| / |G_P|  =  2 / 6  =  1 / 3.
```

**This is exactly at the strategy's threshold.** Step 2's
required bound is `|λ_sign| ≤ δ < 1/3`. The N-poset attains
`|λ_sign| = 1/3` exactly — strict inequality fails.

### 2.3 Fix-point-excess bound (irrep `[n-1, 1]`)

```
E[fix]  =  (4 + 2 + 2 + 2 + 0 + 0) / 6  =  10/6  =  5/3.
```

```
|λ_std|  ≤  (E[fix] − 1) / (n − 1)  =  (2/3) / 3  =  2/9  ≈  0.222.
```

`2/9 < 1/3` strictly. **The fix-point mode is small on the
N-poset.**

### 2.4 Two-cycle-excess bound (irrep `[n-2, 2]`)

```
E[#2c]  =  (0 + 1 + 1 + 1 + 2 + 0) / 6  =  5/6.
```

```
|λ_{[n-2,2]}|  ≤  |E[#2c] − 1| / (n(n−3)/2)  =  (1/6) / 2  =  1/12  ≈  0.083.
```

Small. (The bound is signed in the table — `(E[#2c] − 1)` is
negative here — so the absolute value is the appropriate
read.)

### 2.5 Summary on the K=2 N-poset

| irrep                    | bound      | vs. `1/3` |
|--------------------------|------------|-----------|
| sign `[1^4]`             | **1/3**    | **=**     |
| standard `[3, 1]`        | 2/9 ≈ 0.222| <         |
| two-row `[2, 2]`         | 1/12 ≈ 0.083| <        |

**The ranking inverts the strategy's premise.** The strategy
asserts the **fix-point mode** is the large one (others
small); on the K=2 N-poset, the **sign mode** is the large
one (saturating `1/3`), and the fix-point mode is small.

This is not a marginal failure — `|λ_sign| = 1/3` exactly,
making the inequality `|λ_sign| ≤ δ < 1/3` unsatisfiable for
any `δ < 1/3`. Even granting strict-vs-weak-inequality
slack, `1/3` is the precise threshold the strategy needs to
push past via Cheeger and Theorem E. Saturating it leaves no
slack.

### 2.6 Sibling computations

To check whether the K=2 N-poset is anomalous or
representative, the polecat computed the three bounds on six
siblings (Python enumeration; reproducible).

| Configuration                                                       | n | `|L(P)|` | sign  | fix     | 2-cyc   | irreducible? | strict ⪯-pair? |
|--------------------------------------------------------------------|---|----------|-------|---------|---------|--------------|----------------|
| **K=2 N-poset** (`x_i < y_i`, i=1,2)                                | 4 | 6        | **1/3** | 2/9    | 1/12    | yes (∗)      | no            |
| **F1 minimal** `{a, a', y}` with `a' < y`                           | 3 | 3        | **1/3** | 1/6    | n/a (∗∗)| yes          | yes (`upper(a)=∅⊊{y}=upper(a')`) |
| Claw `{x; y_1, y_2, y_3}`, `x < y_i`                                | 4 | 6        | 0     | 1/3    | 1/4     | NO (ordinal sum `{x} ⊕ Antichain_3`) | no |
| K=2 5-elem `x_1<y_1, x_1<y_2, x_2<y_3`                              | 5 | 20       | 0     | 17/80 ≈ 0.21 | 0.04 | yes        | no (`upper(x_1)={y_1,y_2}` and `upper(x_2)={y_3}` are incomparable) |
| K=2 3 disjoint chains `x_i < y_i`, i=1,2,3                          | 6 | 90       | 1/15 ≈ 0.067 | 0.12 | 0.035 | yes        | no            |
| K=2 N-poset + extra `x_1<y_2`                                       | 4 | 5        | 1/5   | **1/3** | 0       | yes          | yes (`upper(x_2)={y_2}⊊{y_1,y_2}=upper(x_1)`) |
| K=2 5-elem hub `x_1<y_1, x_1<y_2, x_2<y_2, x_3<y_2`                 | 5 | 18       | 0     | 1/4     | 0.022 (abs) | yes        | yes (multiple) |

(∗) The K=2 N-poset is irreducible per
`feedback_n_poset_is_not_ordinal_sum`; it is the canonical
"smallest non-ordinal-sum width-2 poset" obstruction.
(∗∗) The `[n-2, 2]` irrep is undefined for `n ≤ 3`.

**Patterns visible from the data:**

* **Small-`n` strict-pair configs saturate `|λ_sign| = 1/3`
  exactly.** Both the K=2 N-poset (n=4) and the F1 3-element
  minimal (n=3) hit the threshold.
* **Asymptotically (larger `n`), `|λ_sign|` shrinks.** The
  3-disjoint-chains case (n=6, |β|=3) has `|λ_sign| = 1/15 ≈
  0.067`. Some 5-elem configs (5-elem hub, irreducible 5-elem
  with `x_1<y_1, x_1<y_2, x_2<y_3`) have `|λ_sign| = 0`.
* **The fix-point mode is sometimes large, sometimes small.**
  On reducible configs (claw — actually `{x} ⊕ A_3` ordinal
  sum) and on the N-poset + extra-edge config, the fix-point
  bound saturates `1/3`. On irreducible 5- and 6-element K=2
  configs it is ≤ 1/4. **No uniform "fix-point dominates"
  pattern emerges across the K=2 family.**
* **The 2-cycle bound is consistently small** (≤ 1/4 across
  the board, often `< 0.1`). This part of the strategy
  appears robust.

### 2.7 Bound-rigor concern (precondition for Step 1 even being meaningful)

The eigenvalue bounds in `notes/bk-walk-irrep-eigenvalue-bounds.md`
treat the BK walk on `L(P)` as if it were the random
transposition walk on full S_n, where the spectrum is given
by class-function characters via Diaconis–Shahshahani.
**It is not.** Three discrepancies:

1. **State space.** `L(P) ⊆ S_n` is a *subset*, not a
   subgroup. For non-subgroups, S_n irreps do not directly
   diagonalise the indicator's regular-representation
   isotypic decomposition. The sum
   `Σ_{g ∈ L(P)} (−1)^{sgn(g)} / |L(P)|` is well-defined as
   a real number, but interpreting it as a BK-walk eigenvalue
   needs a separate argument.
2. **Transition kernel.** The BK walk's transitions are
   **adjacent** transpositions `τ_i = (i, i+1)`, not arbitrary
   transpositions. Adjacent transpositions are not a
   conjugacy class, so even on full S_n the spectrum of the
   adjacent-transposition walk (the "interchange / random
   adjacent walk") is **not** given by a clean character
   formula — Diaconis–Shahshahani's theorem is for the
   random transposition walk, not for adjacent.
3. **Restriction to `L(P)`.** The BK walk further restricts
   the transitions to those that preserve LE-ness (i.e., the
   two elements at positions `i, i+1` are incomparable in P).
   This induces a non-uniform edge weighting on `L(P)`, and
   the resulting walk is reversible w.r.t. uniform measure
   on `L(P)` but its spectrum needs separate analysis.

The polecat **could not locate** a published derivation of
the form "the BK walk on `L(P) ⊆ S_n` has irrep-component
eigenvalue bounded by the empirical statistic on `L(P)`."
Daniel's note labels this the **optional Step 5** ("S_n ↔ BK
matching"). For Step 1 to be a meaningful input to Step 2,
Step 5 must be done first.

This is, separately, a Step-5 escalation trigger per the
ticket: deriving such bounds rigorously is a non-trivial
research question that may need fresh published-literature
theorems (e.g. interlacing / quotient-walk / Caputo-style
spectral bounds for restricted walks). Polecat scoping
authority does not extend to that derivation.

**Net effect on Step 1.** Even granting the bounds at face
value (as we do throughout §2–§3), Step 2 fails on the K=2
N-poset. So the question of whether the bounds are rigorous
is, for the verdict, moot — the strategy is RED at Step 2
*either way*. We flag the rigor gap in §6 / §8 because it
matters for any follow-on attempt.

---

## 3. Step 2 verdict — RED

> **Step 2 (per ticket).** Prove the parity / sign and 2-cycle
> bounds are both `≤ δ < 1/3` on the obstruction family,
> leaving only the fix-point mode potentially large.

### 3.1 The K=2 N-poset triggers the stop-loss directly

Per ticket §Stop-loss/block-and-report-triggers:

> **Step 2 fails on the K=2 N-poset.** Specifically: if the
> sign-imbalance or 2-cycle bound is itself large (≥ 1/3) on
> the N-poset, the strategy's "only fixed-point can be large"
> premise is wrong — STOP, report.

§2.2 computed `|λ_sign| = 1/3` on the K=2 N-poset, **exactly
at the threshold**. The strict inequality `≤ δ < 1/3` fails
for any `δ`. The stop-loss fires.

### 3.2 The premise inverts on irreducible configs

Beyond the threshold-saturation: on the K=2 N-poset the
**ordering** of which mode is large is opposite to the
strategy's expectation:

* Strategy expects: fix-point mode large; sign and 2-cycle
  modes small.
* K=2 N-poset reality: **sign mode at threshold (1/3);
  fix-point mode small (2/9); 2-cycle mode small (1/12)**.

The strategy's Step 3 ("large E[fix] ⇒ layered rigidity") is
therefore aimed at the wrong mode — even if the N-poset's
sign-imbalance were `< 1/3` strictly, Step 3 would still need
a parallel "large parity ⇒ rigidity" theorem to handle the
case where parity is the dominant mode. No such theorem is
stated in the strategy.

The same inversion appears on the F1 minimal counterexample
(§2.6): `|λ_sign| = 1/3` exactly, fix-point bound 1/6.
**Two of the canonical small-K=2 configurations exhibit the
inversion.**

### 3.3 No slack: `|Σ(P)|/|G_P|` is an exact identity, not a slack bound

Granting the table's premise that `|λ_sign|` is bounded by
the sign-imbalance ratio, the bound is in fact an **equality**
when interpreted as "the sign character of the indicator
function `1_{L(P)}` in `L²(S_n)` has L²-norm `|Σ(P)|/√|G_P|`,
hence the sign-isotypic projection has norm `|Σ(P)|/|G_P|`".
There is no slack to push the bound below `1/3` on the N-poset
without changing the framing entirely (e.g. swapping in a
different invariant for the sign mode).

This is a structural feature of the K=2 N-poset, not an
artefact of bound looseness.

### 3.4 Asymptotic regime — does the bound shrink with `n`?

Yes. From §2.6:

* `|λ_sign|` on K=2 3-disjoint-chains (n=6): `1/15 ≈ 0.067`.
* `|λ_sign|` on K=2 5-elem irreducible: `0`.
* `|λ_sign|` on K=2 5-elem hub: `0`.

So **as `n` grows in the K=2 family, `|λ_sign|` shrinks below
`1/3` on at least some natural sub-families.** A refined
strategy could restrict Step 2's claim to "K=2 obstruction
family with `n ≥ n_0` for some threshold `n_0`", treating the
small-`n` cases (K=2 N-poset, F1 minimal) by direct
enumeration as **outside** the spectral-strategy purview.

This is comparable to how Theorem E itself is asymptotic
(`η(γ, n) = 2/(γn) ↓ 0`): for n=4, `η(1/3, 4) = 1.5` is
trivially satisfied (every conductance is ≤ 1), so Theorem E
provides no traction on the K=2 N-poset directly anyway. The
small-n cases are handled by Lean enumeration
(`Case3Enum.lean`); the spectral strategy only needs to
fire on sufficiently-large-`n` members of the obstruction
family.

**However**, this "asymptotic-only" refinement comes with two
problems:

1. **The polecat cannot establish the `n_0` threshold**
   without doing the math. Heuristically, `n_0 ≥ 12` is
   plausible (since F2's Brightwell vacuity exits at `|Q| ≥ 12`
   too — though the underlying mathematics is unrelated). But
   actually proving `|λ_sign| < 1/3` uniformly for K=2
   irreducible obstruction-family members at `n ≥ n_0`
   requires either a structural argument (which the strategy
   doesn't supply) or a generating-function / asymptotic
   character calculation (paper-level math, escalation).
2. **Even if Step 2 holds asymptotically, Steps 3 and 4 still
   need to fire on those large-`n` members.** The strategy's
   Step 3 ("large E[fix] ⇒ layered rigidity") is *not*
   bounded above by the K=2 N-poset failure — it's a
   substantive separate question. §4 discusses why Step 3 has
   its own RED concern (collapse to Steps 5–7 in spectral
   clothing).

So even if Step 2 is rescued in the asymptotic regime, Steps 3
and 5 (rigor of bounds) remain blockers, and small-n cases
remain outside the strategy's reach (which is fine, since
Lean enumeration handles them — but it means the strategy is
not the clean "Cheeger-via-character" alternative the table
suggested).

### 3.5 Step 2 verdict

**RED, per ticket stop-loss trigger.**

* On the K=2 N-poset: `|λ_sign| = 1/3` (at threshold), strategy
  premise inverted (fix-point mode small, sign mode dominant).
* On the F1 3-element minimal: same — `|λ_sign| = 1/3`.
* Across K=2 siblings: no uniform "fix-point dominates"
  pattern; sometimes sign dominates, sometimes fix, sometimes
  all are small.
* The asymptotic-regime escape clause (Step 2 holds for `n ≥
  n_0`) is plausible but **the polecat cannot establish it
  without paper-level math**, and it is not what the strategy
  as posed asserts (the strategy asserts uniform Step 2, not
  asymptotic).

The polecat **stops** here per ticket §Constraints. Steps 3
and 4 are addressed below for completeness, and Step 5 is
discussed in §6.

---

## 4. Step 3 verdict — deferred / RED-risk

> **Step 3 (per ticket).** Prove that if `E[fix(g)] − 1` is
> large, the poset has structural rigidity matching the
> layered-decomposition setup (so G3-style reductions or
> direct ordinal-sum lifts fire).

Step 3 is moot once Step 2 fails. We address it briefly to
flag a separate concern that would block the strategy even if
Step 2 were rescued.

### 4.1 The intuition

`E[fix(g)] = Σ_i Pr[posₗ(a_i) = i]` (relative to a reference
LE `L_0`). If `E[fix]` is large (much greater than 1), some
elements have positions strongly concentrated to specific
indices in random LEs. Concentration → rigidity → layered
decomposition is the idea.

Heuristic check on the claw (§2.6): `E[fix] = 2`, fix-bound `=
1/3`. The claw is `{x} ⊕ Antichain_3` — an exact ordinal sum,
so layered with `K = 2` and `Aut = S_3` (on the upper band).
Step 3 would correctly infer "layered rigidity" here. ✓

But the claw is **reducible** — already dispatched by the
existing G3 / `lem:layered-reduction` machinery
(`step8.tex`'s deep-layered branch). So Step 3 firing on the
claw doesn't help; the case is already in tree.

### 4.2 The arc 1.0 D / arc 3.0 D6 collapse risk

Per ticket §Stop-loss:

> **Re-derives Steps 5-7's rigidity content via spectral
> language.** This is the arc 1.0 D / arc 3.0 D6 trap. If the
> proof of step 3 ("large E[fix] ⇒ rigidity") collapses to
> invoking the existing Steps-5-7 machinery, that's a sign
> the spectral framing is just relabelling; report and STOP.

The polecat cannot prove or disprove this without doing
the math, but the structural shape is suspicious:

* Steps 5–7 of the in-tree proof prove a Cheeger-style
  conductance lower bound from rigidity / fiber-coherence /
  globalisation. Their content is *exactly*: structural input
  → spectral output (high conductance / large gap).
* Step 3 of Daniel's strategy would prove the converse:
  spectral input (large `E[fix]`) → structural output (layered
  rigidity). To prove it without invoking Steps 5–7 would
  require an *independent* combinatorial argument from
  position-concentration to layered structure.
* Such an independent argument would be a non-trivial new
  theorem of poset combinatorics. The polecat could not
  locate it in Brightwell, Kahn–Saks, Felsner–Trotter, or the
  Bubley–Karzanov literature.

There is a more conservative reading: maybe Step 3 is
*partially* independent (`E[fix]` concentration
arguments using e.g. Lindeberg-style conditioning), and the
remaining gap is bridgeable by light Steps-5-7-flavoured
machinery. But that bridge is the load-bearing content of
Steps 5–7 and would either reproduce them or require a
substantive simplification of them.

### 4.3 Step 3 verdict

**Deferred (Step 2 failed); independent concern: RED-risk by
arc 1.0 D / arc 3.0 D6 collapse.** A future polecat or
researcher revisiting the strategy must demonstrate that Step
3's proof does **not** invoke or reproduce Steps 5–7. The
polecat could not locate a published path that achieves this.

---

## 5. Step 4 verification — Cheeger consumption is in tree

> **Step 4 (per ticket).** In the residual case, all eigenvalue
> modes are small ⇒ spectral gap on BK walk ⇒ balanced pair
> via Theorem E (in tree).

This step is the only one that does not introduce new content.
It uses:

* **Cheeger lower bound for BK walk.** `Φ(BK(P)) ≥ (1 − λ_2)/2`,
  standard for reversible chains. (Cheeger's inequality; see
  e.g. Levin–Peres, *Markov Chains and Mixing Times*, ch. 13.)
  Spectral gap `1 − λ_2` large ⇒ conductance `Φ` large.
* **Theorem E contrapositive.** `step8.tex` `thm:cex-implies-low-expansion`:
  width-3 indecomposable γ-counterexample on `n ≥ 2` elements
  ⇒ a cut `S` with `Φ(S) ≤ η(γ, n) = 2/(γn)`. Contrapositive:
  if every cut has conductance `> 2/(γn)`, the poset is **not**
  a γ-counterexample, i.e. it has a balanced pair.

**Consumption.** If Steps 1–3 deliver `λ_2(BK(P)) ≤ ε(n)`
with `ε(n) → 0`, then Cheeger gives `Φ(BK(P)) ≥ (1 −
ε(n))/2`. For this to exceed `2/(γn)`, we need

```
(1 − ε(n)) / 2  >  2 / (γn),
ε(n)            <  1 − 4/(γn).
```

For `γ = 1/3` and `n ≥ 13`, `4/(γn) = 12/n ≤ 12/13 < 1`, so
the RHS is positive — *some* `ε(n)` works. The strategy needs
the bound `ε(n) < 1 − 12/n` (taking `γ = 1/3 − o(1)`) for all
sufficiently large `n` in the obstruction family.

**In tree.** `lean/OneThird/Step8/MainAssembly.lean` consumes
Theorem E (`thm:cex-implies-low-expansion`) via the
`StructuralBalancedTheorem` pipeline. Step 4 of Daniel's
strategy would slot in as an alternative producer of "balanced
pair exists" given a spectral-gap input — but this requires
piping `λ_2(BK(P))` into the pipeline, which the in-tree
machinery currently does **not** expose as a public
interface (the in-tree path goes structural-input →
conductance directly, bypassing the eigenvalue).

This is an engineering note, not a strategy obstruction —
adding the spectral-gap-to-conductance Cheeger lemma in tree
is mechanical. The mathematical content of Step 4 is sound.

**Step 4 verdict.** GREEN (modulo Step 2/3 producing the
input). The Cheeger consumption is well-understood and the
in-tree Theorem E receives it cleanly.

---

## 6. Step 5 — S_n ↔ BK matching (deferred to follow-on)

> **(Optional) Step 5.** S_n dynamics match BK — relate the BK
> walk on L(P) to a canonical S_n walk so the table's bounds
> transfer rigorously.

Per ticket §Stop-loss-triggers:

> **Optional step 5 (S_n ↔ BK matching) is harder than steps
> 1–4.** Polecat may report on steps 1–4 and explicitly defer
> step 5 to a follow-on if step 5 alone explodes the budget.

The polecat **defers** Step 5 with the following framing of
why it is the load-bearing technical question:

### 6.1 Why Step 5 is required for Steps 1–2 to make sense

Per §2.7, the table's eigenvalue bounds treat the BK walk as
if it were the random transposition walk on full S_n. The
gaps:

| issue                      | random transposition on S_n | BK walk on L(P)             |
|----------------------------|----------------------------|------------------------------|
| state space                | full S_n (subgroup)        | L(P) ⊆ S_n (subset)         |
| transition kernel          | uniform-random transpositions | adjacent transpositions, restricted to LE-preserving |
| spectrum                   | irrep characters (Diaconis–Shahshahani) | unknown in general |
| `|λ_sign| = |Σ|/|G|` ?     | yes (subgroup-character identity) | not directly — needs derivation |

### 6.2 Possible matching strategies (none in tree, none in
literature the polecat could locate)

* **Comparison by Cheeger / canonical paths** (Diaconis–Saloff-Coste).
  Compare BK on L(P) to the random transposition walk on a
  larger ambient space, transferring eigenvalue bounds. This
  is a substantial machinery and gives only crude bounds.
* **Caputo-style spectral comparison** (Caputo–Liggett 2008
  for the interchange process; Cesi 2009 for random
  transposition walks on graphs). Gives spectrum bounds for
  walks on subgraphs of the Cayley graph of S_n, but assumes
  conditions (e.g. attractive interaction) that don't
  obviously transfer to LE-restricted walks.
* **Direct character-theoretic computation on L(P)**, treating
  `1_{L(P)}` as a vector in `L²(S_n)` and projecting onto
  irrep isotypic components. The projections give *the
  empirical statistics* (e.g. `Σ(P) / |L(P)|` is the
  sign-isotypic component magnitude), but their connection
  to **BK-walk eigenvalues** (rather than ambient
  transposition-walk eigenvalues) requires further argument
  — *exactly what the strategy needs and lacks*.

### 6.3 Polecat verdict on Step 5

**Out of scope for polecat authority.** Per ticket §Constraints:

> **No paper-level math discovery** under polecat authority.
> If steps 2 / 3 require a substantively new theorem from
> representation theory or spectral methods that doesn't exist
> in published literature, **STOP** and escalate.

The polecat believes Step 5 is **the** load-bearing
prerequisite for Steps 1–2 to be even well-defined. Without
it, the eigenvalue bounds are heuristic targets, not theorems.

A research-level follow-on with substantive representation-
theoretic and spectral-comparison expertise could potentially
produce Step 5; the polecat does not. This is a Daniel-only
escalation point.

---

## 7. Aggregate verdict

**RED.** The strategy as posed fails at Step 2 on the
explicitly-named obstruction-family base case (the K=2
N-poset), where `|λ_sign| = 1/3` exactly — saturating the
threshold and inverting the strategy's "fix-point dominates"
premise.

The verdict is supported by:

* **Direct computation** (§2.2–§2.6): seven configurations
  enumerated; the K=2 N-poset and F1 3-element minimal both
  attain `|λ_sign| = 1/3`.
* **Stop-loss trigger** (per ticket §Stop-loss): the K=2
  N-poset failure is the explicit RED-condition.
* **Mode inversion** (§3.2): on irreducible K=2 cases the
  sign mode is large, not the fix-point mode; the strategy's
  Step 3 is aimed at the wrong mode.
* **Step 3 collapse risk** (§4.2): even if Step 2 were
  rescued, Step 3 risks reproducing Steps 5–7's content in
  spectral clothing (arc 1.0 D / arc 3.0 D6 trap).
* **Step 5 prerequisite** (§6): the table's eigenvalue bounds
  are heuristic targets, not theorems, until Step 5
  (S_n ↔ BK matching) is established. Polecat scoping
  authority does not extend to Step 5.

### Concrete next-chunk recommendation if a future researcher revisits

If Daniel revisits this strategy (or a successor), the
prerequisites are:

1. **Fix Step 5 first.** Without rigorous bounds linking
   BK-walk eigenvalues to empirical statistics on L(P), Steps
   1–2 are undefined. This is paper-level math (escalation).
2. **Asymptotic regime, not uniform.** Step 2 cannot hold
   uniformly across the K=2 family (N-poset and F1 minimal
   saturate `1/3`). A refined claim "Step 2 holds for `n ≥
   n_0`" is consistent with §2.6's data but requires
   independent proof.
3. **Step 3 independence audit.** Demonstrate that "large
   `E[fix]` ⇒ layered rigidity" admits a proof that does not
   invoke or reproduce Steps 5–7. If it does, the strategy is
   the arc 3.0 D6 trap in different clothes.
4. **Handle the dominant-sign-mode case separately.** Even if
   Step 2's parity bound is proved small for large `n`, the
   strategy needs to reckon with the small-n case where the
   sign mode is the threshold-saturating one. (Lean
   enumeration handles small-n on the in-tree path; the
   spectral strategy must either match or replace that.)

**Aggregate: RED.** Not GREEN, not AMBER. The premise
("only fix-point mode can be large") is not supported by the
direct computation on the obstruction-family base case, and
the rigor / collapse / S_n-matching concerns each independently
threaten the strategy.

---

## 8. Risk inventory and comparison to F1/F2/F3

The arc 4.0 strategy was evaluated against the same three
structural facts that closed arcs 1.0–3.0 (per
`docs/why-hC3-is-structural.md`).

| obstruction | arc 4.0 navigation                                                                                 | verdict |
|-------------|---------------------------------------------------------------------------------------------------|---------|
| **F1** (cardinality / no order-preserving swap on strict ⪯-pair) | The spectral framing avoids the Aut(P)-based reduction altogether — uses `L(P) ⊆ S_n` rather than `Aut(P)`. **Genuinely navigates around F1.** | ✓ avoided |
| **F2** (Brightwell vacuity at K=2 / `|Q| ≤ 6`)                  | Cheeger's `Φ ≥ (1 − λ_2)/2` does not invoke `brightwell_sharp_centred`. The strategy uses BK-walk spectrum, not single-element perturbation. **Genuinely navigates around F2.** | ✓ avoided |
| **F3** (published `[0.276, 1/3)` gap)                            | The strategy is a Cheeger / spectral attack like the existing paper — **same flavour as the published path**, not a refinement of correlation inequalities. F3 doesn't directly bite; arc 4.0 is in the same family as the paper's existing approach. | ✓ avoided |

So the strategy *would* navigate F1, F2, F3 if it worked. But
arc 4.0 introduces **two new obstructions** of its own:

| obstruction (arc 4.0) | source                                  | severity |
|-----------------------|-----------------------------------------|----------|
| **F4-a** (Step 2 RED) | K=2 N-poset has `|λ_sign| = 1/3`; strategy premise inverts on irreducible configs | **terminal** |
| **F4-b** (Step 3 RED-risk) | "Large E[fix] ⇒ layered rigidity" risks collapsing to Steps 5–7 in spectral clothing (arc 1.0 D / arc 3.0 D6 trap) | high |
| **F5** (Step 5 prerequisite) | Eigenvalue bounds on `BK(L(P))` are not derived from S_n character theory; need separate spectral-comparison machinery (paper-level math) | high |

**F4-a alone is sufficient to RED the strategy.** F4-b and F5
are independent additional concerns.

### 8.1 Comparison to arc 3.0's eight ε-close definitions and twelve strategy alternatives

Arc 3.0 §3 surveyed twelve strategy alternatives (S1–S12). Of
those, **none were spectral / character-theoretic on `L(P) ⊆
S_n` directly**. The closest were:

* **S5 (count-form FKG)** — different normalisation, RED.
* **S6 (Brightwell-pump)** — different perturbation, RED via F2.
* **D6 (spectral defect)** — bounds `λ_2` from cardinality;
  tautological, RED.

Arc 4.0's character-on-`L(P)` framing is a **new entry** in
this taxonomy, not a re-tread of S5/S6/D6. The novelty is
real (per §1.5). But the verdict is still RED, just from a
different obstruction (F4-a) than arc 3.0's framings.

### 8.2 The N-poset's recurring centrality

Across all four arcs, the **K=2 N-poset** (4 elements,
`x_i < y_i` for i=1,2) has been the recurring focal
counterexample:

* Arc 1.0 D (Candidate D rejected): N-poset blocks compound
  automorphism by F1.
* Arc 2.0: N-poset's `|Q| = 4` is below F2's `|Q| ≥ 12`
  threshold.
* Arc 3.0 D6: N-poset's λ_2 doesn't bound from cardinality.
* **Arc 4.0 (this arc): N-poset saturates `|λ_sign| = 1/3`,
  inverting the fix-point-dominates premise.**

The K=2 N-poset is small (4 elements) and irreducible, giving
it a unique role: it is too small for asymptotic machinery
(F2 size, Theorem E `n_0`, conductance asymptotics) but
irreducible enough to defeat structural reductions
(F1, claw-vs-antichain). Per
`feedback_n_poset_is_not_ordinal_sum` it is the canonical
"smallest nontrivial K=2 obstruction".

Future arcs targeting `hC3` should treat the K=2 N-poset as
the **first stop-loss test**, not a curiosity.

---

## 9. References and memory anchors

### Internal documents

* `notes/bk-walk-irrep-eigenvalue-bounds.md` (mg-7e24,
  2026-05-04) — Daniel's working table; Step-1 input.
* `step8.tex` §G1 (`thm:cex-implies-low-expansion`) — Theorem E
  in tree (Cheeger half).
* `lean/OneThird/Step8/MainAssembly.lean` — pipeline that
  consumes Theorem E.
* `docs/path-c-track-1-status-1.md` §2 (mg-b666) — F1
  cardinality obstruction.
* `docs/why-hC3-is-structural.md` (mg-cda8) — F1/F2/F3
  synthesis.
* `docs/math-simp-arc-3.0/scoping.md` §2.6 (mg-65e1) — D6
  spectral-defect prior negative finding.

### Memory anchors applied

* `feedback_latex_first_for_math_simp` — applied (no Lean
  changes; deliverable is a markdown scoping doc).
* `feedback_audit_bar_for_axioms` — applied (no new project
  axioms attempted; Step 5 escalated, not unilaterally
  added).
* `feedback_signature_regressions` — applied (no replacement
  hypothesis for `hC3` proposed; verdict is RED, no
  signature change).
* `feedback_n_poset_is_not_ordinal_sum` — applied (the K=2
  N-poset's irreducibility status is the structural fact
  driving §3.2's "premise inversion on irreducible
  configurations").
* `feedback_distinguish_arc_chunk_outcomes` — applied
  (outcome class: substantive scoping, no parallel cleanup;
  RED verdict reported honestly without parallel-shipping
  attempt).

### Cross-references to other tickets

* `mg-7e24` — landed input table (`notes/bk-walk-irrep-eigenvalue-bounds.md`).
* `mg-ea39` — Daniel's adjacent conceptual-development
  workspace (parent strategy context).
* `mg-cda8` — F1/F2/F3 synthesis; verifies arc 4.0
  navigates around all three.
* `mg-65e1` — arc 3.0 scoping; D6 prior negative is the
  closest neighbour.
* `mg-b666` — Track 1 cardinality obstruction (F1).
* `mg-3e53` — arc 1.0 scoping (Candidate D — this arc is
  a Candidate-D variant in spirit).
* Daniel directive 2026-05-05T~00:00Z (in-session, no
  reminder ID).

### Reproducibility note

The Step-1 computations (§2.2–§2.6) were enumerated by direct
LE / S_n calculation. The polecat's enumeration script was
ephemeral; a reader can reproduce it by enumerating
`permutations({1..n})` constrained by the cover relations of
each poset, and computing `sign`, `fix`, `#2-cycles` of each
LE's induced `σ ∈ S_n` against a fixed reference `L_0`. All
results in §2 are integer / rational and reproducible.

### What this doc does NOT claim

Per discipline `feedback_distinguish_arc_chunk_outcomes` and
arc 3.0 §4.5:

* Does **not** claim that no spectral / character-theoretic
  strategy can work — only that **Daniel's specific strategy
  as posed** is RED on the K=2 N-poset.
* Does **not** claim that Step 5 (S_n ↔ BK matching) is
  unprovable — only that it is paper-level math outside
  polecat authority.
* Does **not** claim that Step 3 is unprovable — only that
  the polecat could not locate a published path that proves
  it without invoking Steps 5–7.
* Does **not** claim that arc 4.0 obviates F1/F2/F3 — the
  strategy navigates around them (§8) but encounters its own
  obstructions (F4-a, F4-b, F5).
* Does **not** propose any change to `hC3` retention,
  AXIOMS.md, or the headline. Outcome class: scoping doc only.

---

*This file is the deliverable for `mg-0bc8`, filed on
2026-05-05 by polecat `p0bc8` on branch `math-simp-arc-4.0`.
It is doc-only (no Lean source changes) and follows the arc
2.0 / arc 3.0 / mg-cda8 precedent of "scoping-as-deliverable"
under polecat authority.*
