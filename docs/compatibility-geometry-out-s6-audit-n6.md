# Compat-Geom — Out(S_6) audit at n=6 (mg-3219)

**Status:** GREEN-Out-robust.

**Branch:** `compat-geom-out-s6-audit-n6` (from `compat-geom-F8p-hpc-n6`).

**Depends:** mg-3bf3 (F8'-HPC, `50118d2`) — COMPLETE. Its brief already
carried a first-pass Out(S_6) outer-twin check (`docs/
compatibility-geometry-F8prime-HPC.md` §4); this audit builds directly
on that and deepens it from *cited folklore* to *machine-verified from
first principles*.

**Daniel reminder 2026-05-14T02:53Z:** "small note — n=6 could be an
unusual case due to the odd Aut(S_6)."

**Scope.** Audit the effect of the non-trivial outer automorphism of
S_6 on the n=6 cohomological program (Burnside / Lefschetz sign-rep
extraction, per-step Pr / BFT-sharpness, PPF_6 → PPF_7 inductive lift).
No new axioms. 80k cap.

**Script:** `scripts/posn_n6_out_s6_audit.py` — runs in seconds on top
of `scripts/_n6_cache/ppf6.pkl` (produced by `posn_n6_hpc.py
--phase=enum`). All six audit checks below are hard asserts in that
script; it exits non-zero if any fails.

---

## 0. Executive summary

S_6 is the unique symmetric group with `Out(S_6) ≅ ℤ/2`. The audit
question: does the outer automorphism perturb the n=6 cohomological
program? Four deliverables, all resolved:

| # | deliverable | result |
|---|-------------|--------|
| 1 | re-verify χ̃(Fix_PPF_6(σ)) per class, incl. outer-twin pairs | ✅ verified; identity = χ̃(Fix(σ)) = (−1)^{n−2}·sgn(σ), Out-invariant |
| 2 | does m_sgn = 1 carry to n=6 | ✅ yes (Out-invariantly); identity-class χ̃ inherited AMBER from mg-3bf3 |
| 3 | per-step Pr, Out(S_6)-orbit-by-orbit | ✅ question is vacuous — Out(S_6) does not act on PPF_6; Pr-profile is a single S_6-orbit datum, 4/4 BFT-sharp |
| 4 | PPF_6 → PPF_7 (I5) inductive lift × Out(S_6) | ✅ Out-*detectable* in the lift's combinatorial presentation, but *not obstructive* — ω_bal lives in the Out-fixed sign summand |

**Verdict: GREEN-Out-robust.** Out(S_6) introduces **no deviation** in
the n=6 Burnside / Lefschetz data and **no obstruction** to the
inductive-lift framework. The one place Out(S_6) is genuinely *visible*
(§5, the point-stabiliser-vs-exotic-S_5 distinction) is a presentation
artifact, not a cohomological perturbation.

A second, independent finding (§3): the apparent sign discrepancy
between the mg-3219 ticket (n=5: `χ̃(Fix) = −sgn`) and the mg-3bf3 doc
(n=6: `χ̃(Fix) = +sgn`) is **not** an Out(S_6) effect — it is the
degree-parity factor (−1)^{n−2} of the Hopf–Lefschetz trace formula,
present at every n. mg-3bf3's doc states the n=5 identity with the
wrong sign and presents an even-n-only Burnside formula as universal;
this is flagged as a documentation slip (§3.3) that does **not** touch
mg-3bf3's n=6 result.

---

## 1. The outer automorphism, constructed explicitly

mg-3bf3 §4 *cited* the folklore fact that Out(S_6) swaps three
conjugacy-class pairs. This audit constructs an explicit outer
automorphism and verifies the swap data from first principles.

**Construction (§A of the script).** S_6 has the type-A_5 Coxeter
presentation on adjacent transpositions s_0,…,s_4. An automorphism is
fixed by its values on the s_i. We search for triple-transposition
images t_i = α(s_i) satisfying the braid relations
(s_i² = e, (s_i s_{i+1})³ = e, (s_i s_j)² = e for |i−j| ≥ 2) and
generating all of S_6. One solution:

```
s_0 = (0 1)            t_0 = (0 1)(2 3)(4 5)
s_1 = (1 2)            t_1 = (0 2)(1 4)(3 5)
s_2 = (2 3)            t_2 = (0 1)(2 5)(3 4)
s_3 = (3 4)            t_3 = (0 2)(1 3)(4 5)
s_4 = (4 5)            t_4 = (0 1)(2 4)(3 5)
```

Because each t_i is a triple-transposition (not a transposition) and an
inner automorphism preserves cycle type, **α is outer**. The script
extends α to all 720 elements by Cayley-graph BFS and hard-checks it is
a bijective homomorphism.

**Class-swap verification (§B).** Pushing each of the 11 conjugacy-class
representatives through the explicit α reproduces *exactly* mg-3bf3's
`OUTER_TWIN_PAIRS` and `OUT_FIXED` data:

| outer-twin pair (swapped by α) | |class| | sgn |
|--------------------------------|--------:|:---:|
| (2,1⁴) transposition ↔ (2³) triple-transposition | 15 / 15 | −/− |
| (3,1³) 3-cycle ↔ (3²) (3,3)-cycle | 40 / 40 | +/+ |
| (6) 6-cycle ↔ (3,2,1) | 120 / 120 | −/− |

| Out-fixed classes | 1⁶ · 2²,1² · 4,1² · 5,1 · 4,2 |
|---|---|

α preserves sgn and class size on **every** class (forced: A_6 is
characteristic in S_6, and any automorphism permutes same-size
classes). This confirms the folklore mg-3bf3 relied on.

---

## 2. Deliverable 1+2 — χ̃(Fix_PPF_6(σ)) and m_sgn at n=6

### 2.1 Per-class table, re-verified

Independently re-running `posn_n6_hpc.py --phase=burnside` (PPF_6
enumeration → 129 302 elements, matching mg-3bf3) reproduces the
per-class fixed-point data exactly:

| class | cycle shape | |class| | sgn | |Fix| | χ̃(Fix) | χ̃ = sgn? |
|-------|:-----------:|--------:|:---:|------:|:------:|:--------:|
| 1⁶ | identity | 1 | + | 129 302 | SKIP (HPC; see §2.3) | — |
| 2,1⁴ | transposition | 15 | − | 4 230 | −1 | ✓ |
| 3,1³ | 3-cycle | 40 | + | 218 | +1 | ✓ |
| 2²,1² | double transposition | 45 | + | 414 | +1 | ✓ |
| 4,1² | 4-cycle | 90 | − | 18 | −1 | ✓ |
| 5,1 | 5-cycle | 144 | + | 2 | +1 | ✓ |
| 6 | 6-cycle | 120 | − | 0 | −1 | ✓ |
| **2³** | **triple-transposition** | **15** | **−** | **150** | **−1** | **✓** |
| **3,2,1** | (3,2,1) | **120** | **−** | **18** | **−1** | **✓** |
| **3²** | (3,3) | **40** | **+** | **14** | **+1** | **✓** |
| 4,2 | (4,2) | 90 | + | 6 | +1 | ✓ |

The clean Lefschetz identity `χ̃(Fix(σ)) = sgn(σ)` holds at all 10
computed classes (identity deferred — §2.3).

### 2.2 Out-invariance of χ̃(Fix)

χ̃(Fix(·)) is a **class function** on S_6 (Fix(σ) and Fix(τστ⁻¹) have
isomorphic order complexes). The audit's §C check: this class function
is **invariant under the explicit α** — for every class C,
χ̃(Fix(C)) = χ̃(Fix(α(C))). In particular all three outer-twin pairs
agree:

```
χ̃(Fix(2,1⁴)) = χ̃(Fix(2³))   = −1     ✓   (|Fix| = 4 230 vs 150)
χ̃(Fix(3,1³)) = χ̃(Fix(3²))   = +1     ✓   (|Fix| =   218 vs  14)
χ̃(Fix(6))    = χ̃(Fix(3,2,1))= −1     ✓   (|Fix| =     0 vs  18)
```

Note the |Fix| **cardinalities differ wildly** within a twin pair
(4 230 vs 150). What is Out-invariant is not the size of the fixed
poset but the **reduced Euler characteristic of its order complex** —
a topological invariant. This is the precise content of "no Out(S_6)
deviation": the fixed-point *combinatorics* is Out-sensitive; the
fixed-point *topology* (as it enters Burnside) is not.

**Why this is forced, not lucky.** Under the F-series concentration
hypothesis, H̃_*(Δ_6) is concentrated in degree 4 and equals m_sgn
copies of the sign rep. The sign rep is **Out(S_6)-fixed** — A_6 is the
unique index-2 subgroup of S_6, hence characteristic, so *every*
automorphism (inner or outer) preserves sgn. Therefore χ̃(Fix(σ)) =
(−1)⁴·m_sgn·sgn(σ) is automatically a class function fixed by Out(S_6).
The per-class verification above is the empirical confirmation that no
*other* irreducible component sneaks into the virtual cohomology and
breaks this — and none does.

### 2.3 m_sgn(n=6) = 1, Out-invariantly

Summing over the 10 computed (non-identity) classes:

```
Σ_{σ ≠ id} sgn(σ)·χ̃(Fix(σ)) = Σ_{C ≠ id} |C|·sgn_C·χ̃(Fix(σ_C)) = 719 = |S_6| − 1
```

every term equalling |C| (since sgn_C·χ̃(Fix(σ_C)) = +1 at all 10
classes). With the identity-class extrapolation χ̃(Δ_6) = +1:

```
m_sgn(n=6) = (1/720)·(719 + 1) = 1.
```

**m_sgn = 1 carries to n=6**, and because §2.2 shows the entire
per-class χ̃(Fix) data is Out-invariant, m_sgn = 1 is itself
Out(S_6)-invariant — the Burnside sum picks up no non-cancelling
outer-twin contribution. This is exactly the risk flagged in the
mg-3219 ticket ("m_sgn might differ from 1 at n=6"); it does not
materialise.

**Residual (inherited, not Out-specific).** The identity-class
χ̃(Δ_6) is not computed directly — |Fix(id)| = |PPF_6| = 129 302 makes
the order-complex DP an HPC-multi-hour job (mg-3bf3 §3.3, §6.1;
`state-F8prime-HPC.md` Q1). The extrapolation χ̃(Δ_6) = +1 rests on the
n=4 / n=5 clean-Lefschetz precedent and the 10/11 verified classes.
**This residual is an HPC-budget item, not an Out(S_6) obstruction** —
1⁶ is an Out-fixed class, so it cannot host an outer-twin asymmetry.

---

## 3. The sign convention — a degree-parity effect, not an Out effect

### 3.1 The apparent discrepancy

The mg-3219 ticket states the n=5 identity as

> χ̃(Fix_PPF_5(σ)) = **−**sgn(σ)

while the mg-3bf3 doc states (and the n=6 table confirms) the n=6
identity as

> χ̃(Fix_PPF_6(σ)) = **+**sgn(σ).

These look contradictory. They are not.

### 3.2 Reconciliation via Hopf–Lefschetz

For a simplicial automorphism σ of Δ_n, the Lefschetz fixed-point
theorem gives χ̃(Fix(σ)) = Σ_i (−1)^i tr(σ | H̃_i(Δ_n)). When H̃_* is
concentrated in degree n−2 and equals m_sgn copies of the sign rep,

```
        χ̃(Fix_PPF_n(σ))  =  (−1)^{n−2} · m_sgn · sgn(σ).
```

The degree-parity factor (−1)^{n−2} is the whole story:

| n | n−2 | (−1)^{n−2} | clean identity (m_sgn = 1) |
|---|-----|:----------:|----------------------------|
| 4 | 2 | +1 | χ̃(Fix) = +sgn |
| 5 | 3 | **−1** | χ̃(Fix) = **−sgn**  ← mg-3219 ticket |
| 6 | 4 | +1 | χ̃(Fix) = +sgn  ← mg-3bf3 doc / §2 table |

The ticket's "−sgn" (n=5) and mg-3bf3's "+sgn" (n=6) are **the same
identity**, evaluated at opposite parities of n−2. The script's §D
check confirms the n=6 per-class table matches (−1)^{n−2}·m_sgn·sgn
exactly. **This flip is intrinsic to every n and has nothing to do
with Out(S_6)** — it would occur identically for S_5 (which has no
outer automorphism).

This matters for the audit because it is precisely the kind of "n=6
looks unusual" symptom that could be *mistaken* for an Out(S_6) effect.
It is not. Disentangling the two is a core audit outcome: the only
genuine n=6 anomaly is Out(S_6); the sign flip is a red herring shared
with odd n.

### 3.3 Flagged: documentation slip in mg-3bf3 (n=6 result unaffected)

Two lines in `docs/compatibility-geometry-F8prime-HPC.md` / `posn_n6_hpc.py`
are correct only for **even n**:

1. The stated clean identity "χ̃(Δ(Fix(σ))) = +sgn(σ) for all σ ∈ S_n
   [n ∈ {4, 5}]" — wrong at n=5, where it is −sgn.
2. The Burnside formula "m_sgn = +(1/|S_n|)·Σ sgn(σ)·χ̃(Fix(σ))"
   presented as universal — the correct general form carries the
   degree-parity factor: m_sgn = (−1)^{n−2}·(1/|S_n|)·Σ sgn·χ̃.
   (Also: the `posn_n6_hpc.py` verbose header column is labelled
   `-sgn?` while the code checks `χ̃ == +sgn` — a cosmetic
   label/check mismatch.)

**mg-3bf3's n=6 verdict is unaffected.** Both of its compute points —
the n=4 calibration and the n=6 result — sit at *even* n, where
(−1)^{n−2} = +1, so the even-n-only formula gives the right answer.
The n=5 line was never on mg-3bf3's computation path; it is a
documentation slip, recorded here, not a computational error. A
one-line correction to the mg-3bf3 doc is recommended as cleanup
(out of scope for this audit ticket — noted, not fixed).

---

## 4. Deliverable 3 — per-step Pr, Out(S_6)-orbit-by-orbit

### 4.1 The question is vacuous — and that is the answer

The mg-3219 ticket asks for the n=6 BFT-sharp characterisation
"Out(S_6)-orbit-by-orbit, not chain-by-chain", anticipating that
canonical chains might pair up into Out-twins with differing Pr-values.

**This cannot happen, for a structural reason: Out(S_6) has no action
on PPF_6 at all.** Out(S_6) is an automorphism of the *abstract group*
S_6; it does not act on the ground set {0,…,5}. The S_6-action on PPF_6
(and hence on chains, cells, and c*_6) is the *standard permutation
action* on {0,…,5}. The outer automorphism does not preserve this
action — it carries the standard 6-point action to the inequivalent
"exotic" 6-point action. Consequently there is **no Out(S_6)-action on
PPF_6, on its chains, or on c*_6** to split the Pr-profile into orbits.

So the requested restatement is: *the Pr-profile cannot split into
Out(S_6) orbits; BFT-sharpness is trivially Out(S_6)-stable.* The
"chain-by-chain vs orbit-by-orbit" distinction collapses because the
only group acting on chains is S_6 itself.

### 4.2 The Pr-profile, on its single S_6-orbit

Re-verified by `posn_n6_out_s6_audit.py` §E (and `posn_n6_hpc.py
--phase=pr`):

| k | |L(P_k)| | Pr_k | in [3/11, 8/11]? |
|---|--------:|:----:|:----------------:|
| 0 | 180 | — | — |
| 1 | 84 | 7/15 | ✓ BFT |
| 2 | 48 | 4/7 | ✓ BFT |
| 3 | 24 | 1/2 | ✓ BFT |
| 4 | 12 | 1/2 | ✓ BFT |

**4/4 BFT-sharp**, matching mg-7b3b and mg-3bf3. c*_6 generates a
single S_6-orbit; the Pr-profile is an S_6-invariant of that orbit.

### 4.3 Where Out(S_6) *does* touch the Pr framework: Stab(c*_6)

The one Out-meaningful question about c*_6 is its **stabiliser**.
`posn_n6_out_s6_audit.py` §E computes

```
Stab(c*_6) = {id}      (trivial — the ordered 4-cell c*_6 has no
                        non-identity S_6-symmetry)
```

which is **trivially ⊆ A_6** — in fact stronger than mg-3bf3 §6.3's
claim "Stab(c*_6) ⊂ A_6". A trivial stabiliser means the signed
S_6-orbit sum ω_naive^(6) = Σ_{g ∈ S_6} sgn(g)·g·c*_6 is well defined
with no sign ambiguity, and the orbit has full size 720. Out(S_6) acts
on the *conjugacy class* of Stab(c*_6) in the abstract group — but the
trivial subgroup is Out-fixed, so even this is a no-op.

---

## 5. Deliverable 4 — PPF_6 → PPF_7 inductive lift × Out(S_6)

### 5.1 Out(S_6) is detectable in the lift's combinatorial presentation

The inductive lift ι_n: PPF_n → PPF_{n+1} adds a fresh ground-set
element with no relations. It is **equivariant for the point-stabiliser
S_n ⊂ S_{n+1}** — the subgroup fixing the newly added point. At the
n=6 base, ι_5: PPF_5 → PPF_6 is equivariant for a point-stabiliser
S_5 ⊂ S_6.

Out(S_6) swaps the **two conjugacy classes of S_5 ⊂ S_6**: the six
point stabilisers ↔ the six "exotic" transitive S_5's. The script's §F
check verifies this with the explicit α: pushing Stab(5) through α
yields an order-120 S_5 subgroup that **fixes no ground-set point**
(it is transitive). So:

> α carries the lift's equivariance subgroup *out* of the
> point-stabiliser class. There is **no** add-an-element lift map
> equivariant for the exotic S_5.

This is a **genuine, visible structural effect of Out(S_6)** — it is
the n=6 anomaly Daniel's reminder anticipated. In the verdict
taxonomy's language it is "visible structural perturbation".

### 5.2 …but it is a presentation artifact, not a cohomological obstruction

The lift framework's *purpose* is to transport the cohomology class
ω_bal^(n) ∈ H̃^{n−2}(Δ_n)^sgn to ω_bal^(n+1). The combinatorial
presentation of the lift (which S_5 it is equivariant for) is
Out-sensitive; its **cohomological output is not**:

- ω_bal lives in the **sign-rep summand** H̃^{n−2}(Δ_n)^sgn.
- sgn is **Out(S_6)-fixed** (A_6 characteristic in S_6).
- m_sgn = 1 is Out-invariant (§2.2–2.3).

So Out(S_6) acts trivially on the object the lift actually transports.
The question "does ι_5 lift to Aut(S_6)-equivariance" is, strictly,
**not well-posed** — there is no Aut(S_6)-action on PPF_6 to be
equivariant *with respect to* (cf. §4.1). The well-posed version —
"is the transported class ω_bal Out(S_6)-stable" — has answer **yes**,
because it is a sign-rep class.

### 5.3 The n=7 end is Out-trivial

Out(S_n) is trivial for all n ≠ 6. So PPF_6 → PPF_7 has an outer twin
only at the *base*; the n=7 target carries no outer automorphism and
no outer-twin classes. The (I5) Quillen-fiber gap (identify X_n with
Δ_{n+1}/Δ_n ≃ ΣΔ(X_n)) is a Tier-3 specialist obstruction for
general-n structural lift — but it is **not** an Out(S_6) obstruction:
it is the *same* gap at every n, and n=6 contributes no extra
difficulty beyond the presentation subtlety of §5.1.

**Reading for the verdict:** §5.1 is the one place Out(S_6) is
*detectable* — strictly an AMBER-Out-detectable signal at the level of
the lift's combinatorial presentation. §5.2–5.3 show it does **not**
break the inductive-lift framework: the cohomological program is
robust. Net: the detectable effect is benign.

---

## 6. Verdict

`scripts/posn_n6_out_s6_audit.py` — six hard-assert checks, all PASS:

| § | check | result |
|---|-------|:------:|
| A | explicit outer automorphism α constructed + verified bijective homomorphism + outer | PASS |
| B | α swaps exactly mg-3bf3's 3 twin pairs, fixes the other 5 classes | PASS |
| C | χ̃(Fix_PPF_6(·)) is Out(S_6)-invariant (all 11 classes) | PASS |
| D | n=6 per-class table matches (−1)^{n−2}·m_sgn·sgn | PASS |
| E | Stab(c*_6) ⊆ A_6 (in fact trivial); c*_6 Pr-profile 4/4 BFT-sharp | PASS |
| F | α maps the point-stabiliser S_5 off its class (detectable, not obstructive) | PASS |

### Verdict: GREEN-Out-robust

- **Burnside / Lefschetz (deliverables 1–2):** χ̃(Fix_PPF_6(·)) is
  Out(S_6)-invariant across all 11 classes; m_sgn(n=6) = 1 carries over
  Out-invariantly. The clean identity is χ̃(Fix(σ)) = (−1)^{n−2}·sgn(σ)
  — at n=6, +sgn.
- **Per-step Pr (deliverable 3):** Out(S_6) does not act on PPF_6, so
  the Pr-profile cannot split into Out-orbits; the (7/15, 4/7, 1/2,
  1/2) profile is 4/4 BFT-sharp on the single S_6-orbit of c*_6.
- **Inductive lift (deliverable 4):** Out(S_6) is *detectable* in the
  lift's combinatorial presentation (point-stabiliser S_5 ↦ exotic
  S_5) but is *not an obstruction* — the transported class ω_bal lives
  in the Out-fixed sign-rep summand. Out(S_7) is trivial.
- **Sign-rep is Out(S_6)-invariant** (A_6 characteristic in S_6), which
  is the structural reason all of the above is forced rather than
  coincidental.

**Not AMBER-Out-detectable** as an overall verdict: the only detectable
effect (§5.1) is a presentation artifact with no cohomological
consequence. **Not RED-Out-obstruction:** nothing breaks.

**Residual gaps — inherited, not Out-specific:**
1. χ̃(Δ_6) for the identity class — HPC-budget item from mg-3bf3
   (§3.3 / §6.1 of that doc; `state-F8prime-HPC.md` Q1). 1⁶ is
   Out-fixed, so it cannot host an outer-twin asymmetry.
2. Chamber-Morse concentration of H̃_*(Δ_6) in degree 4 — mg-3bf3
   AMBER-budget-cap §6.2. The Out-invariance of χ̃(Fix) (§2.2) holds
   as a *virtual-representation* statement regardless; concentration
   only sharpens "virtual cohomology" to "cohomology".

Neither residual is an Out(S_6) obstruction.

**Recommended cleanup (out of scope here):** correct the two even-n-only
lines in mg-3bf3's doc / `posn_n6_hpc.py` flagged in §3.3.

---

## 7. References

### Scripts
- `scripts/posn_n6_out_s6_audit.py` — this audit (§A–§F, six checks).
- `scripts/posn_n6_hpc.py` — mg-3bf3 master script (enum / burnside /
  pr phases re-run here for independent verification).

### Predecessors
- **mg-3bf3 (F8'-HPC)** — `50118d2` — `docs/compatibility-geometry-F8prime-HPC.md`;
  first-pass Out(S_6) outer-twin check (§4), m_sgn(n=6) = 1.
- **mg-7b3b (F8')** — `7a8607f` — n=6 ICOP empirical, 4/4 BFT-sharp.
- **mg-1e99 (F8)** — `cce0377` — inductive ω_bal at general n; (I5) gap.
- **mg-73fd / mg-e8d5 (F7 / F7')** — n=5 Burnside / Plan B literal cocycle.

### Literature
- M. Janusz, J. Rotman, *Outer automorphisms of S_6*, Amer. Math.
  Monthly 89 (1982) — Out(S_6) ≅ ℤ/2 classification.
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).
- A. Björner, M. Wachs, *Shellable nonpure complexes and posets I, II*.
