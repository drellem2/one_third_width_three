# Compat-Geom — F9 Session 2: the n=7 pattern test — polynomial vs exponential (mg-14a0)

**Branch:** `compat-geom-F9-S2-n7-pattern` (target); polecat branch `polecat-cat-mg-14a0`, based on F9 Session 1 (`5a94ce9`).
**Parent:** mg-9e88 (F9 Session 1; **GREEN-Plan-H-at-n=6** at `5a94ce9`).
**Session predecessor state:** `docs/state-F9.md` (cumulative ledger; updated by this session).
**Type:** Constructive numerical execution + structural cross-pattern (LaTeX-first; **no new axioms**; no Lean changes; pure-Python stdlib supplement).
**Verdict:** **AMBER-pattern-shifts** — the F9 empirical Plan-H pattern is **n=5/n=6-specific**. Plan H at n=7 *does* admit a ℚ-solution (so this is **not** RED-pattern-breaks), and the *skeleton* of the Session-1 mechanism survives — the constraint matrix still has full row rank and there is still exactly one nonzero ψ wing-orbit per F7-bad coface. But the **near-diagonal structure degrades sharply** (anomaly count 0 → 1 → **211**; a new ψ-coefficient **+2** appears) **and the bad-coface count grows decisively super-polynomially**: the third and fourth count datapoints rule out polynomial growth — the 3-point quadratic interpolant predicts u₈ = 4633, the actual u₈ = **65099** (14×). The empirical correction therefore has **no clean closed form in n**. This is the F9-fallback datum (state-F9.md decision rule): the direct constructive Plan-H route does **not** close (I5) at general n; the parked X_n / specialist route is now indicated. Surfaced to PM.

**Daniel directive 2026-05-14T05:18Z:** "finish induction even if it's hard; no external collab yet" — F9 attempted the (I5) lift directly via the Plan H empirical correction. Session 2 is the decisive datapoint: it shows the direct route does not generalize, which is itself a real, methodology-paper-grade result.

---

## 0. Executive summary

### 0.1 What Session 2 set out to decide

F9 Session 1 (mg-9e88) executed Plan H at n=5 and n=6, built the explicit S_n-equivariant sign-rep corrections ψ^(5), ψ^(6), and detected a **shared structural mechanism**:

- **(M1)** the Plan H constraint matrix has full row rank;
- **(M2)** the number of nonzero ψ wing-orbits equals the number of F7-bad cofaces exactly;
- **(M3)** the lex-first ℚ-solution is **near-diagonal** — at n=5 a pure diagonal (every bad coface has exactly one codim-1 face in supp(ψ)); at n=6, 63/64 diagonal + a single isolated off-diagonal entry (the −2 coefficient).

What Session 1 could **not** decide is the n-dependence of the **count** of F7-bad cofaces — 10 (n=5) → 64 (n=6), dominated by the position-(n−1) up-set u_n of the top poset (4 → 54). **Two datapoints cannot distinguish polynomial from exponential growth.** The mg-9e88 critical-insight criterion: polynomial growth ⇒ the pattern admits a closed form and (I5) closes constructively via the mechanism; exponential growth ⇒ the Plan H system at general n is intractable and (I5) needs a different angle.

Session 2 computes the **third datapoint at n=7** (and, cheaply, a fourth at n=8) and tests whether the Session-1 mechanism is *predictive* — not merely *descriptive* — at n=7.

### 0.2 Headline results (all computationally verified — `scripts/posn_constructive_lift_n7.py`)

| Quantity | n = 5 | n = 6 | **n = 7** |
|---|---:|---:|---:|
| c*_n rank profile | (3,5,6,8) | (3,5,6,8,9) | **(3,5,6,8,9,10)** |
| Stab(c*_n) | trivial ✓ | trivial ✓ | **trivial ✓** |
| \|S_n · c*_n\| | 120 | 720 | **5040** |
| immediate cofaces of c*_n = **F7-bad** count B_n | 10 | 64 | **1607** |
| — interior-position cofaces | 6 | 10 | **10** |
| — top-position up-set u_n | 4 | 54 | **1597** |
| wing chains | 40 | 320 | **9642** |
| wing S_n-orbits (sign-supported) | 38 (36) | 316 (314) | **9074 (9016)** |
| Plan H linear system | 10 × 36, rank 10 | 64 × 314, rank 64 | **1607 × 9016, rank 1607** |
| nonzero ψ wing-orbits | 10 | 64 | **1607** |
| \|supp(ψ^(n))\| | 1200 | 46080 | **8 099 280** |
| d(ω_naïve + ψ) = 0 on F7-bad set | 10/10 ✓ | 64/64 ✓ | **1607/1607 ✓** |
| ⟨ω_naïve + ψ, c*_n⟩ | +1 ✓ | +1 ✓ | **+1 ✓** |
| ψ-coefficient set | {−1,+1} | {−2,−1,+1} | **{−2,−1,+1,+2}** |
| near-diagonal anomalies (bad cofaces with ≥2 faces in supp ψ) | **0** | **1** | **211** |

Fourth count datapoint (count-only, no Plan H solve at n=8): **u₈ = 65099**.

### 0.3 The two findings that fix the verdict

**Finding A — the count is decisively super-polynomial.**

The bad-coface count and its dominant term, the top-position up-set, are:

```
B_n :  10,  64,  1607              ratios  6.40,  25.11
u_n :   4,  54,  1597,  65099      ratios 13.50,  29.57,  40.76
```

The ratios are **strictly increasing** in both sequences — the hallmark of super-polynomial growth (a polynomial's consecutive ratios decay monotonically toward 1). The decisive test: the unique quadratic interpolant through the three points (5,4), (6,54), (7,1597) — the *only* low-degree polynomial consistent with the n≤7 up-set data — **predicts u₈ = 4633**. The actual u₈ = **65099** — **14.05× larger**. Polynomial growth of the count is decisively ruled out; the data is consistent with exponential (or faster) growth.

**Finding B — the near-diagonal structure shifts meaningfully.**

The Session-1 mechanism does **not** simply persist:

- **(M1) full row rank — survives.** rank 1607 = #constraints. ✓
- **(M2) one nonzero ψ orbit per bad coface — survives.** 1607 = 1607. ✓
- **(M3) near-diagonal ±1 solution — degrades sharply.** The per-bad-coface count of codim-1 faces in supp(ψ) is `{1: 1396, 2: 211}` — **211 of 1607 (13%)** bad cofaces are *off-diagonal*, versus **0** at n=5 and **1** at n=6. A new ψ-coefficient **+2** appears (coefficient set {−2,−1,+1,+2}). The "isolated low-order correction" of Session 1 has become a *substantial, growing off-diagonal population*.

The Session-1 description — "ψ^(n) is, up to *isolated* low-order corrections, one sign-rep wing-orbit cochain per bad coface, with unit coefficient" — is **not** what ψ^(7) looks like. The qualifier "isolated" fails at n=7.

### 0.4 Verdict: AMBER-pattern-shifts

Against the mg-14a0 verdict spec:

| Tag | Condition | This run |
|---|---|:--:|
| **GREEN-pattern-polynomial** | count compatible with polynomial growth AND near-diagonal pattern persists | ✗ — count super-polynomial; near-diagonal degrades |
| **GREEN-pattern-detected-but-count-uncertain** | near-diagonal pattern holds, count growth not yet clear | ✗ — near-diagonal does not hold; count growth *is* clear (super-poly) |
| **AMBER-pattern-shifts** | near-diagonal structure changes meaningfully (many anomalies, not one isolated −2); pattern is n=5/n=6-specific | ✓ **THIS RUN** — 211 anomalies; new +2 coeff; super-poly count |
| **RED-pattern-breaks** | Plan H at n=7 fails to admit a ℚ-solution OR d(ω_M^(7)) ≠ 0 unachievable | ✗ — Plan H *is* solvable; d(ω_M^(7)) = 0 achieved on all 1607 |

**Verdict: AMBER-pattern-shifts.** The F9 empirical Plan-H pattern is **n=5/n=6-specific**. Note carefully what is and is not claimed:

- **Plan H itself still works at n=7** — the linear system is solvable, full row rank, and the explicit ψ^(7) closes d(ω_naïve^(7) + ψ^(7)) = 0 on all 1607 F7-bad cofaces with the pairing preserved. RED-pattern-breaks is *not* triggered.
- **What fails is the *pattern* — the closed-form predictiveness.** Both the *count* (super-polynomial, Finding A) and the *near-diagonal shape* (Finding B) of the correction are n=5/n=6-specific. The Session-1 mechanism does not extrapolate to a general-n closed form.

The *programmatic consequence* coincides with the mg-14a0 RED-pattern-breaks prose even though the RED *trigger* is not met: "genuinely flips program; specialist route (PARKED per Daniel) becomes inevitable; document for methodology paper as a real obstruction." The direct constructive Plan-H route — attempted per the Daniel 2026-05-14T05:18Z directive — **does not close (I5) at general n**. This is itself a clean, decisive result.

### 0.5 Trust-surface impact

**None.** Pure structural cohomology computation building on mg-9e88 / mg-e8d5; no new axioms; no Lean changes; pure-Python stdlib.

---

## 1. Setup

### 1.1 Recap — the Plan H pipeline (parameterized at arbitrary n)

F9 Session 1's `scripts/posn_constructive_lift_n6.py` implements the Plan H empirical-correction pipeline as a single routine `run_plan_h(n, chain, label)` applicable at any n, taking the canonical critical (n−2)-cell c*_n = (P_0 ⊊ ⋯ ⊊ P_{n−2}):

1. **ω_naïve^(n)** — the signed S_n-orbit cochain Σ_γ sgn(γ)·δ_{γ(c*_n)}^∨, well-defined in the sign-rep iff Stab(c*_n) ⊆ A_n.
2. **Immediate cofaces** — insert one proper PPF_n element Q at one of the n positions; for the top position Q ranges over the proper up-set of P_{n−2}.
3. **F7-bad set** — cofaces τ with (dω_naïve^(n))(τ) ≠ 0.
4. **Wings** — codim-1 faces of bad cofaces not in S_n·c*_n; decompose into S_n-orbits; keep sign-supported ones.
5. **Solve** — the ℚ-linear system: one constraint per bad coface, one unknown per sign-supported wing orbit; ψ(γ·w_j) = sgn(γ)·c_j; exact Gaussian elimination.
6. **Verify** d(ω_naïve^(n) + ψ^(n)) = 0 on the bad cofaces and ⟨ω_naïve^(n)+ψ^(n), c*_n⟩ = ±1.

Session 2's `scripts/posn_constructive_lift_n7.py` **imports** this machinery (the dependency is fully within-branch — Session 1's deliverable sits on this branch) and adds the n=7 cell, a memory-efficient solver, the 3-datapoint cross-pattern, and the count-function extrapolation.

### 1.2 The candidate critical 5-cell c*_7

Per the F8'-HPC / F8-framework recipe (one step up from `c_star_6_chain`):

> c*_7 = ( ι_6(P_0), …, ι_6(P_4), P_4 ∪ {lex-min step-5 cover} )

where (P_0,…,P_4) = c*_6 is the F9 Session-1 cell, ι_6 lifts it to the ambient {0,…,6} leaving element 6 free, and the **lex-min step-5 cover** is the lexicographically smallest ordered pair addable to P_4 giving a proper, antisymmetric, transitively-closed poset. For P_4 = c*_6[−1] the pairs (0,1),(0,2),(0,3),(0,4) are already present, so the lex-min addable pair is **(0,5)** — in exact agreement with the F8 general-n script `posn_inductive_omega_bal_general_n.py` §E, which states the lex-min cover at this step "is e.g. (0,5)".

c*_7 has rank profile **(3,5,6,8,9,10)** — a dim-5 cell — with element 6 incomparable throughout. Its first 5 posets *are* c*_6 (ι_6 is the identity on relation sets); see trip-wire (c).

### 1.3 Memory-efficient solver (`solve_psi_fast`)

The Session-1 `solve_psi`/`orbit_decomposition` accumulates the *full* S_n-orbit of every wing in a `seen` set. At n=7 that is ~9000 orbits × up to 5040 = **~48M chains** — gigabytes of memory, which thrashes. (Two contributing subtleties: the Session-1 `canonical_rep` is a *no-op* on equal-rank-profile chains, because `frozenset.__lt__` is subset-order, not lex-order, so each chain becomes its own "rep" and the work is entirely in the orbit-enumeration `seen` set.)

`solve_psi_fast` replaces this with `_group_wings`, whose `seen` set holds **only wing chains** (≤ #wings): for each not-yet-grouped wing (the orbit's first-encountered representative — exactly the Session-1 choice) it sweeps S_n once, recording the images that are themselves wings and the stabilizer inline. Memory is O(#wings); the orbit encounter order, the rep choice, and the per-wing signs all match Session 1 exactly. **Verified exact-arithmetic identical to Session 1 at n=5 and n=6** (trip-wire (a)). The n=7 wing grouping runs in ~5 min.

---

## 2. Trip-wire pre-checks (mandatory)

All three mg-14a0 trip-wires **PASS**.

**(a) n=5 and n=6 Plan H reproduce Session 1 exactly.** Running the parameterized Plan H at n=5 (F7's Hasse c*_5) and n=6 (the F8'-HPC c*_6) reproduces mg-9e88 / mg-e8d5 verbatim: n=5 — 10 F7-bad cofaces, 10 × 36 system rank 10, |supp(ψ^(5))| = 1200, pure-diagonal solution, pairing +1; n=6 — 64 F7-bad cofaces, 64 × 314 system rank 64, |supp(ψ^(6))| = 46080, 63/64 diagonal + 1 isolated −2, pairing +1. Both reproduced *through the new `solve_psi_fast` code path* — the n=7 numbers are therefore produced by a solver verified against two prior independent results.

**(b) ω_naïve^(7) well-defined.** Stab(c*_7) = {id} ⊂ A_7. ω_naïve^(7) is well-defined in C^5(Δ_7;ℚ)^sgn with |S_7·c*_7| = 5040. This *positively rules out* RED-foundational.

**(c) the ι_6-lift c*_6 → c*_7 is well-defined.** Verified: the first 5 posets of c*_7 *are* c*_6 (`prefix_is_c6: True`); the appended P_5 strictly refines P_4 (`P5_strictly_refines_P4: True`), is antisymmetric and proper (`P5_antisymmetric / P5_proper: True`), and the refinement adds exactly the single pair (0,5) with no closure expansion (`added_pairs: [(0,5)]`, `single_pair_cover: True`). c*_7 is a genuine one-step coface of (the ι_6-lift of) c*_6.

---

## 3. Plan H at n=7: the construction of ψ^(7)

### 3.1 The 1607 F7-bad cofaces

The immediate cofaces of c*_7 decompose by insertion position:

| Position | # cofaces | dω_naïve^(7) |
|:--:|:--:|:--:|
| 0 (Q ⊊ P_0) | 6 | +1 |
| 1 (P_0 ⊊ Q ⊊ P_1) | 2 | −1 |
| 3 (P_2 ⊊ Q ⊊ P_3) | 2 | +1 |
| 6 (Q ⊋ P_5, proper) | **1597** | ±1 |
| **total** | **1607** | — |

**All 1607** immediate cofaces are F7-bad (dω_naïve^(7) ∈ {+1,−1}). The interior-position contribution is **10** — identical to n=6 (6+2+2), confirming the interior count has *stabilized* at 10 for n ≥ 6. The entire growth of the bad-coface count is the **top-position up-set u_n** = the proper up-set of P_5, which is **u_7 = 1597**.

### 3.2 The linear system and its solution

Collecting the codim-1 faces of the 1607 bad cofaces not in S_7·c*_7 gives **9642 wing chains** in **9074 S_7-orbits**, of which **9016 are sign-supported**.

The Plan H system is **1607 constraints × 9016 unknowns**, of **rank 1607 (full row rank)**. It is solvable; the lex-first ℚ-solution assigns a nonzero ψ-value to exactly **1607 of the 9016** sign-supported wing orbits — one per F7-bad coface. Sign-rep extension gives

> |supp(ψ^(7))| = 8 099 280 chains in Δ_7.

The ψ-coefficients are **{−2, −1, +1, +2}** — a *new* coefficient +2 relative to ψ^(6)'s {−2,−1,+1}.

### 3.3 Verification

```
d^5( ω_naïve^(7) + ψ^(7) )  =  0   on all 1607 F7-bad 6-cofaces of c*_7    (1607/1607)
⟨ ω_naïve^(7) + ψ^(7),  c*_7 ⟩  =  +1
```

Both verified directly with exact ℚ-arithmetic. So Plan H *is* executed at n=7: the explicit ψ^(7) closes the literal Morse-cocycle equation on the F7-bad set with the pairing preserved. The construction succeeds; it is the *generalizing pattern* that fails (§§4–5).

---

## 4. The 3-datapoint cross-pattern and the mechanism shift

### 4.1 Cross-pattern table

| Quantity | n=5 | n=6 | n=7 | 6/5 | 7/6 |
|---|---:|---:|---:|---:|---:|
| F7-bad cofaces B_n | 10 | 64 | 1607 | 6.40 | 25.11 |
| — interior-position | 6 | 10 | 10 | 1.67 | 1.00 |
| — top-position up-set u_n | 4 | 54 | 1597 | 13.50 | 29.57 |
| wing chains | 40 | 320 | 9642 | 8.00 | 30.13 |
| wing S_n-orbits | 38 | 316 | 9074 | 8.32 | 28.72 |
| sign-supported wing orbits | 36 | 314 | 9016 | 8.72 | 28.71 |
| linear-system constraints = rank | 10 | 64 | 1607 | 6.40 | 25.11 |
| nonzero ψ wing-orbits | 10 | 64 | 1607 | 6.40 | 25.11 |
| \|supp(ψ)\| | 1200 | 46080 | 8 099 280 | 38.40 | 175.77 |

Every "size" quantity grew by a factor 25–30 from n=6 to n=7, versus 6–9 from n=5 to n=6 — the growth *rate itself* is increasing.

### 4.2 The mechanism: (M1)+(M2) survive, (M3) shifts

| Mechanism component | n=5 | n=6 | n=7 | persists? |
|---|:--:|:--:|:--:|:--:|
| **(M1)** full row rank (rank = #bad cofaces) | ✓ 10=10 | ✓ 64=64 | ✓ **1607=1607** | **YES** |
| **(M2)** #nonzero ψ orbits = #bad cofaces | ✓ 10=10 | ✓ 64=64 | ✓ **1607=1607** | **YES** |
| **(M3)** near-diagonal: per-bad-coface faces-in-supp(ψ) | {1:10} | {1:63, 2:1} | **{1:1396, 2:211}** | **NO** |
| — off-diagonal "anomaly" count | **0** | **1** | **211** | growing |
| ψ-coefficient set | {−1,+1} | {−2,−1,+1} | **{−2,−1,+1,+2}** | growing |

The *algebraic skeleton* of the mechanism — the constraint matrix has full row rank, and the lex-first solver selects exactly one pivot orbit per constraint — **does survive** to n=7. That is a genuine (if partial) structural fact and is recorded honestly.

But the *geometric content* that made the mechanism a candidate **closed form** — the **near-diagonality** — does not. Session 1's claim was that ψ^(n) is "*up to isolated low-order corrections*" a unit-coefficient diagonal selection. At n=7 the off-diagonal population is **211 of 1607 ≈ 13%** — not "isolated" — and is plainly growing (0, 1, 211). A new coefficient +2 has entered. The 65 distinct nonzero-orbit rank-profile signatures (vs 7 at n=5, 28 at n=6) show the correction's shape is becoming *more* heterogeneous with n, not converging to a template.

**Conclusion of §4:** the Session-1 mechanism is **descriptive at n ≤ 6 but not predictive at n = 7**. (M1)+(M2) are real but, on their own, do not yield a closed form for ψ^(n) — they only say "the system is well-posed and one-orbit-per-constraint", which still leaves *which* orbit and *what coefficient* per constraint undetermined, and §4.2 shows those are *not* given by a fixed near-diagonal rule.

---

## 5. Count-function extrapolation — the decisive analysis

This is the computation the mg-9e88 verdict spec routed to Session 2: is the bad-coface count polynomial or exponential in n?

### 5.1 The bad-coface count B_n

```
B_n :  10,  64,  1607
Δ¹  :      54,  1543
Δ²  :          1489
ratios B_{n+1}/B_n :  6.40,  25.11   (strictly increasing)
```

The unique interpolating polynomial through the three points is the quadratic with leading coefficient Δ²/2! = **1489/2 = 744.5** — an absurdly large leading coefficient relative to the values themselves (B_5 = 10), and a *non-integer* coefficient for an integer count function. A genuine low-degree polynomial count would have a small leading coefficient and ratios trending toward 1. Here the ratios *accelerate* (6.40 → 25.11). The quadratic interpolant is a degenerate fit — three points always admit *some* quadratic — not evidence of polynomial growth.

### 5.2 The up-set u_n — and the decisive n=8 test

The dominant term is the top-position up-set u_n (the proper up-set of the top poset P_{n−2}). Computing a *fourth* datapoint, u₈ (count-only — `c_star_8_chain()` and its up-set; **no** Plan H solve at n=8, which is out of Session-2 scope):

```
u_n :   4,   54,   1597,   65099
Δ¹  :     50,  1543,  63502
Δ²  :        1493,  61959
Δ³  :             60466
ratios u_{n+1}/u_n :  13.50,  29.57,  40.76   (strictly increasing)
```

**The decisive test.** The 3-point quadratic interpolant through (5,4), (6,54), (7,1597) — the *only* low-degree polynomial consistent with the n ≤ 7 up-set data — **predicts u₈ = 4633**. The actual

> **u₈ = 65099 — 14.05× the quadratic prediction.**

This is no longer "two datapoints cannot distinguish polynomial from exponential". It is **four datapoints with strictly increasing ratios and a quadratic extrapolation that fails by an order of magnitude.** Polynomial growth of u_n — and hence of B_n — is **decisively ruled out**. The data is consistent with exponential (or faster) growth; the cubic interpolant through all four points has leading coefficient 30233/3 ≈ 10078 and is itself surely just another degenerate fit.

### 5.3 Why the up-set explodes (structural reading)

The top poset P_{n−2} of c*_n carries an increasing reservoir of near-free structure: c*_6's P_4 already had the free ι_5-element 5 plus the incomparable pair {3,4} (u_6 = 54); c*_7's P_5 has the free ι_6-element 6, the incomparable pair {3,4}, *and* the now-only-singly-constrained element 5 (only 0 < 5). Each ι-lift step adds a free element that the *next* step only partially constrains, so the proper up-set — the set of proper refinements of P_{n−2} — grows combinatorially, tracking something close to "the number of proper partial orders extending a near-minimal poset on n elements", which is super-polynomial. The interior-position count, by contrast, depends only on the *fixed-size* local refinement intervals of the lower posets, which is why it stabilized at 10.

---

## 6. Verdict and what it means for (I5)

### 6.1 Verdict: AMBER-pattern-shifts

Per §0.4: the near-diagonal structure changes meaningfully at n=7 (211 anomalies, new +2 coefficient — "many anomalies, not just one isolated −2"), and the bad-coface count grows super-polynomially. The F9 empirical Plan-H pattern is **n=5/n=6-specific**. Plan H *itself* is not broken (it solves at n=7 — not RED-pattern-breaks); the *pattern* — the closed-form predictiveness that would close (I5) — is.

### 6.2 Consequence for (I5) and the F9 program

The mg-9e88 critical-insight hypothesis was: *if* the bad-coface count is polynomial, the Session-1 mechanism gives a closed-form description of ψ^(n) and (I5) closes constructively *without* identifying the Quillen-fiber poset X_n. Session 2 falsifies the antecedent on **two independent grounds**:

1. **The count is super-polynomial** (§5) — even a closed-form *count* of the F7-bad cofaces is not low-degree-polynomial, so the Plan H system's *size* grows super-polynomially in n. The orbit-reduced system was 10×36, 64×314, 1607×9016 — and the n=8 system would be ≳ 65000 × (≫10⁵). Tractability degrades fast.
2. **Even given the count, the mechanism is not a closed form** (§4.2) — (M3) near-diagonality, the part that turned "enumerate the bad cofaces" into "ψ^(n) = a fixed diagonal selection", does not generalize. The off-diagonal population grows and a new coefficient appears.

So the **direct constructive Plan-H route does not close (I5) at general n.** Per the Daniel 2026-05-14T05:18Z directive, F9 attempted exactly this direct route; Session 2 is the decisive datapoint that it does not generalize. This *vindicates* the F8'' (mg-b345) scoping of (I5) as a genuine Quillen-fiber / Künneth specialist gap requiring the unknown poset X_n: the empirical correction does **not** substitute for identifying X_n.

This is the **F9-fallback datum** named in the Session-1 state ledger's decision rule ("u_7 super-polynomial OR mechanism fails to predict → empirical correction has no clean closed form → that is the fallback datum … report + surface to PM"). Both disjuncts fire. It is a clean, decisive **negative result** — and, as the mg-14a0 spec anticipated for this outcome, a methodology-paper-grade obstruction: it pins down *why* the inductive lift resists a direct constructive attack and *where* the genuine difficulty (the X_n identification) lives.

### 6.3 What Session 2 does NOT claim

- It does **not** claim Plan H is broken — ψ^(7) is constructed and verified (1607/1607, pairing +1).
- It does **not** claim a *proof* that B_n / u_n is exponential — it claims the data **decisively rules out polynomial** growth (the n=8 quadratic-extrapolation test fails by 14×) and is consistent with exponential.
- It does **not** run a Plan H solve at n=8 (out of Session-2 scope; only the count u₈ is computed).
- It does **not** identify X_n (the parked F8'' route — but it shows that route, or another non-Plan-H angle, is now *necessary*).
- It introduces **no new axioms** and makes **no Lean changes**.

### 6.4 Recommended next step (for PM / roadmap, not this ticket)

Session 3 as originally scoped ("general-n proof or extrapolation table") is **moot for the constructive direction** — there is no general-n closed form to prove. The honest options going forward:

- **Un-park the X_n / specialist route** (F8'' mg-b345) — Session 2 shows it is not optional.
- **Or** a *different* non-empirical angle on (I5) (the mg-9e88 spec's "(I5) needs a different angle").
- Either way, **write up F9 (Sessions 1+2) for the methodology paper** as a documented obstruction: the direct Plan-H empirical-correction route closes (I5) at n=5,6 but provably does not generalize — the count is super-polynomial and the correction's shape is n-specific.

This is surfaced to PM via mg-mail.

---

## 7. Reproducibility

### 7.1 Script

`scripts/posn_constructive_lift_n7.py` — pure-Python stdlib (`fractions.Fraction`, `itertools.permutations`). Imports the Plan H machinery from `scripts/posn_constructive_lift_n6.py` (the Session-1 deliverable, on this branch — within-branch dependency, DRY). Adds `c_star_7_chain()`, `c_star_8_chain()` (count-only), the memory-efficient `solve_psi_fast` / `run_plan_h_fast`, the 3-datapoint `cross_pattern_3`, and `count_function_extrapolation`.

```bash
cd scripts/
python3 posn_constructive_lift_n7.py             # full Session-2 run, ~5 min
python3 posn_constructive_lift_n7.py --verbose   # + per-orbit / per-coface diagnostics
python3 posn_constructive_lift_n7.py --no-n8     # skip the u_8 datapoint
```

The run prints, for each n ∈ {5,6,7}: the Plan H pipeline and ψ-structure analysis; then the trip-wire summary; the 3-datapoint cross-pattern and mechanism-persistence check; the count-function extrapolation (including the u₈ datapoint and the quadratic-extrapolation test); and the verdict tag.

### 7.2 Runtime (Session 2)

| Phase | Wallclock |
|---|---:|
| n=5 + n=6 Plan H (reproduction / trip-wire (a)) | ~1 s |
| n=7 Plan H (wing grouping ~5 min + solve + verify) | ~289 s |
| u₈ count (n=8 up-set BFS, count-only) | ~25 s |
| **total** | **~314 s** |

Token budget: well within the mg-14a0 200k polecat cap.

---

## 8. References

### 8.1 Predecessor mg-tickets

- **mg-9e88 (F9 Session 1)** — `5a94ce9` — Plan H at n=5,6; ψ^(5), ψ^(6); the Session-1 mechanism (M1)–(M3); `posn_constructive_lift_n6.py`; `docs/state-F9.md`; **GREEN-Plan-H-at-n=6**.
- **mg-e8d5 (F7' Plan H, n=5)** — `8d555a7` — the empirical-correction strategy F9 generalizes.
- **mg-3bf3 (F8'-HPC)** — `50118d2` — n=6 Burnside m_sgn = 1; source of `c_star_6_chain`.
- **mg-1e99 (F8 framework)** — `cce0377` — the 8-step inductive ω_bal^(n); (I5) as the single Tier-3 gap; `posn_inductive_omega_bal_general_n.py` §E (the lex-min cover convention used for c*_7).
- **mg-b345 (F8'')** — `45a7532` — (I5) Quillen-fiber / Künneth specialist scoping (X_n) — the route Session 2 shows is now *necessary*.

### 8.2 Daniel directives

- **2026-05-14T05:18Z** — "finish induction even if it's hard; no external collab yet" — attempt (I5) directly via Plan H. Session 2 is the decisive datapoint: the direct route does not generalize.
- `feedback_polecat_cumulative_state_doc` — multi-session cumulative state (`docs/state-F9.md`).
- `feedback_no_external_collab_finish_induction_internally` — specialist outreach parked; Session 2's negative result is what re-opens the question of un-parking it (a PM/roadmap decision, not this ticket).

### 8.3 Code

- `scripts/posn_constructive_lift_n7.py` — **this F9 Session 2 / mg-14a0**.
- `scripts/posn_constructive_lift_n6.py` — mg-9e88 (F9 Session 1) — the imported Plan H machinery.

---

**Verdict: AMBER-pattern-shifts.** Plan H at n=7 is solvable (ψ^(7) constructed, d(ω_naïve^(7)+ψ^(7)) = 0 on all 1607 F7-bad cofaces, pairing +1) — but the F9 empirical pattern is n=5/n=6-specific: the near-diagonal structure degrades sharply (anomalies 0 → 1 → 211; new +2 coefficient) and the bad-coface count grows decisively super-polynomially (u_n = 4, 54, 1597, 65099; the n=8 quadratic-extrapolation test fails by 14×). The direct constructive Plan-H route does **not** close (I5) at general n. F9-fallback datum; surfaced to PM.

Mayor inbox: `mg-14a0`. Branch: `polecat-cat-mg-14a0` → `compat-geom-F9-S2-n7-pattern`.
