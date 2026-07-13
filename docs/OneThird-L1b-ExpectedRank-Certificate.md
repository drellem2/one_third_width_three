# OneThird — BETTER L1b: certify λ_std ≈ 1 with a NON-indicator (expected-rank) test vector

**Work item:** mg-8201 (high, repo `one_third_width_three`). Daniel full-speed, no gate
(directive 2026-07-13). Continuation of the spectral / near-ordinal-sum program for the
1/3–2/3 conjecture. Source: `spectral_near_ordinal_sum_program.tex` (program note);
predecessors mg-b0a6 (kill-shot, ALIVE), mg-3ce3 (L4 stability, GREEN), mg-8b64
(prior-L1b BK→transport, AMBER), mg-7ae7 (reverse-Cheeger attempt). Program-only scope
per Daniel — the Čech/F-series cohomology framings are **not** consulted or routed through.

**Verdict: GREEN-in-regime / AMBER-as-proof — a genuinely better L1b, with the wall named.**

The expected-rank vector `r = T_P u` (`u` = centred position) is a **single global smooth
test vector** whose Rayleigh quotient `R(r)` is a rigorous lower bound on `λ_std(P)`. It
certifies bad mixing **without any prefix / thin-interface object**, so it structurally
avoids the LIB (linear-inversions) bottleneck that made the prior prefix-indicator route
near-circular. Empirically, over 2529 posets:

- `R(r)` captures a **median 93.6 %** of the gap-to-1 (`R(r)/λ_std`), and **never** fails
  on a genuinely badly-mixing poset: among all 829 posets with `λ_std ≥ 0.9`, **zero** have
  `R(r) < 0.6` (min capture 0.81); at `λ_std ≥ 0.99`, min capture 0.85.
- `R(r)` **beats** the crude linear test vector `u` of program §9 in 84 % of posets.
- On the frozen-boundary tower (`δ = 1/3` held fixed, `n → 36`), `1 − R(r) = Θ(1/n²) → 0`.
- The mechanism is an **exact scaling law**: `1 − R(r) = energy(r)/‖r‖²`, with
  `energy(r) = Θ(E[inv_e])` (bounded ratio, median 1.6) and `‖r‖² = Θ(n³)` (→ `n³/12`),
  giving `1 − λ_std ≤ 1 − R(r) = O(E[inv_e]/n³)`. **This tolerates *quadratic* `E[inv_e]`**:
  it still yields `1 − λ_std = O(1/n) → 0` with **no thin prefix** — precisely the point.

The remaining gap to a *proof* is two first-order lemmas (§4), both strictly weaker and
non-circular versus the thin-prefix/LIB requirement: **(A) spread** (`‖r‖² = Ω(n³)`, = the
program's existing monotone-standard-mode conjecture L2) and **(B) locality**
(`E[Σdisp²] = O(E[inv_e])`, new, empirically flat in `n` but unproven at large-`n`
quadratic-`E[inv]`). (B) is the honest wall.

**Skeptical bar (pm-onethird `feedback_empirical_green_is_not_proven`):** every number below
is empirical over a finite ensemble (`n ≤ 9` exhaustive/random + exact ordinal-sum towers to
`n = 36`). A high Rayleigh quotient is **evidence, not a proof**. `R(r)` *is* a rigorous
per-poset lower bound on `λ_std`; but "`R(r) → 1` in-regime" over a finite ensemble is not a
theorem, and §4's proof is contingent on lemmas (A),(B).

---

## 0. What "better L1b" means

The program's falsification chain for a hypothetical **minimal counterexample** `P`
(width-3, `δ(P) < 1/3`, *every* incomparable pair frozen > 2/3 toward a distinguished order
`e = 12⋯n`):

```
minimal counterexample → bad mixing → λ_std(P) ≈ 1 → low-conductance prefix
   → near ordinal sum → balanced pair by minimality → contradiction.
```

`λ_std(P) = max_{f∈H} ⟨f,S_P f⟩/‖f‖²` is the top eigenvalue of the symmetrized
element-position transport block `S_P = (T_P + T_Pᵀ)/2 |_H`, `H = 𝟙^⊥`,
`(T_P)_{x,a} = Pr[x at position a]`. `λ_std = 1` **iff** `P` is an ordinal sum;
`λ_std ≈ 1` **iff** near-ordinal-sum.

**The bottleneck the prior route hit.** L1b = "bad mixing ⟹ `λ_std ≈ 1`." mg-8b64 tried to
force this from a low-conductance **BK pair-indicator** cut, and the honest reading collapsed
to certifying `λ_std ≈ 1` with **prefix-indicator** test functions `1_{A_k}`. But
`R(1_{A_k}) = 1 − Φ_prefix(A_k)`, so a prefix indicator can only certify `λ_std ≈ 1` by
exhibiting a **thin prefix** `A_k` — which is exactly the near-ordinal-sum **conclusion**,
i.e. `E[inv_e] = O(n/γ)` linear inversions ("LIB"). Certifying the hypothesis with the
conclusion is near-circular, and forces an over-strong linear-inversions requirement.

**The fix (Daniel + PM):** stop routing bad mixing through a prefix indicator. Use a
**global smooth** test function that exploits *all-pairs-frozen* rather than one prefix. The
natural one (program §7) is the **expected-rank** vector.

---

## 1. The certificate

Program §4 (transport-energy identity, exact):
```
⟨f,(I − S_P)f⟩ = (1/2|L(P)|) Σ_σ Σ_a (f_a − f_{σ(a)})²   =: energy(f),     f ∈ H.
```
Hence for **any** fixed `f ∈ H`,
```
λ_std(P) ≥ R(f) := ⟨f,S_P f⟩/‖f‖² = 1 − energy(f)/‖f‖².
```
`R(f)` is a **rigorous per-poset lower bound** on `λ_std` — no Cheeger, no prefix, no
BK-transfer. The lead candidate (program §7) is the centred expected-rank vector
```
u_a = a − (n−1)/2   (centred position),   r = T_P u,   r_x = E[pos(x)] − (n−1)/2,
```
which aggregates *all* pairwise biases (`E[pos(x)] = 1 + Σ_{z≠x} Pr[z ≺ x]`). b0a6 found the
dominant standard eigenvector tracks expected rank (Kendall-τ 0.86), so `r` is its natural
smooth proxy. We also evaluate `R(u)` (the §9 crude linear vector), the signed net-bias
vector (an affine image of `r`), and `λ_std` itself (`= R(v)`, the ceiling).

**Script:** `scripts/onethird_mg8201_L1b_expected_rank_probe.py` (reuses the b0a6 engine:
`Poset`, `transport_matrix`, `standard_block_and_lambda`, `before_matrix`, `_LCG`; and the
mg-8b64 `biased_families`). **Data:** `data/onethird-mg8201-L1b-expected-rank.json`.
Ensemble: all both-connected posets `n ≤ 6` (exhaustive), deterministic random
both-connected samples `n = 7,8,9` (LE-capped at 7!), plus **exact** ordinal-sum
frozen-boundary towers to `n = 36` (assembled block-wise — the transport of an ordinal sum
is block-diagonal, so no `n!` enumeration is needed).

---

## 2. STEP 1 — is the prefix/LIB (linear-inversions) route lossy?

`E[inv_e]` = expected number of incomparable pairs appearing opposite to the distinguished
order (= Σ over incomparable pairs of the wrong-way probability; comparable pairs never
invert). The prefix/LIB certificate needs `E[inv_e] = O(n)` (a thin prefix).

**Finding — the reachable frozen regime is thin, so the "super-linear co-occurrence" test is
negative/inconclusive**, but the certificate makes the linear requirement *unnecessary*:

- Within the 829 high-λ posets (`λ_std ≥ 0.9`), `E[inv_e] ~ n^{0.96}` — **near-linear, not
  super-linear** — and `corr(E[inv_e], λ_std) = −0.31` (**negative**: high λ co-occurs with
  *few* inversions, i.e. near-ordinal-sum thinness). We could **not** exhibit a
  high-λ + *quadratic*-`E[inv_e]` poset: the frozen high-λ structures reachable at `n ≤ 9`
  are all thin. So the naive empirical "lossiness signature" is absent in-reach.
- **But the certificate sidesteps this entirely.** `1 − R(r) = energy(r)/‖r‖²` with (§3)
  `energy(r) = Θ(E[inv_e])` and `‖r‖² = Θ(n³)`. So even if `E[inv_e]` *were* `Θ(n²)`
  (the non-thin regime the prefix route cannot handle), `1 − λ_std ≤ 1 − R(r) = O(1/n) → 0`.
  The prefix route's linear-`E[inv_e]` demand is therefore **structurally unnecessary** — the
  expected-rank vector certifies bad mixing across the whole `E[inv_e] = o(n³)` range, which
  for any bounded-width poset is automatic (`E[inv_e] ≤ #incomp pairs = O(n²)`).
- **`R(r)` vs the best prefix indicator** (the LIB route's own object): comparable —
  `R(r) ≥ max_k R(1_{A_k})` in 53 % of posets (median `R(r) = 0.812` vs prefix `0.806`). The
  win is **not** a bigger number; it is that `R(r)` needs *no prefix to exist*.

**Step-1 conclusion:** the prefix/LIB route's linear-inversions requirement is **lossy in the
sense that matters** — unnecessary — because the expected-rank certificate certifies `λ_std`
directly and tolerates quadratic `E[inv_e]`. (The literal "high-λ ∧ quadratic-`E[inv]`"
witness is not exhibitable in-reach; this is a limitation of accessible frozen posets, not
support for LIB.)

---

## 3. STEP 2 — the expected-rank certificate `R(r)`, and its scaling law

### 3.1 `R(r)` is reliable exactly where it must be

| subset | count | median `R(r)` | median `R(r)/λ_std` |
|---|---|---|---|
| all analyzed | 2529 | 0.81 | **0.936** |
| `max_bias ≥ 0.90` | 1856 | 0.805 | 0.935 |
| `δ ≤ 0.40` | 62 | 0.881 | 0.965 |
| `δ ≤ 0.35` | 23 | 0.993 | 0.993 |

- **No false negatives.** Among *all* posets with genuinely high `λ_std`, `R(r)` is always a
  strong certificate: `λ_std ≥ 0.9` → 0 / 829 have `R(r) < 0.6` (min capture 0.81);
  `λ_std ≥ 0.99` → min capture 0.85. Whenever bad mixing is real, `r` sees it.
- **`r` beats the crude linear `u`** (§9) in 84 % of posets (median `R(r) − R(u) = +0.031`),
  confirming expected rank is the right global vector.
- **Where `R(r)` reads small it is *correct* to.** The only near-zero/slightly-negative
  `R(r)` cases are the **fence/zigzag** family (`fence4…8`): `λ_std ≈ 0.39–0.45`
  (good mixing), `δ ≈ 0.4–0.5` (they *have* near-balanced pairs) — **not** the
  counterexample regime. `r` correctly declines to certify bad mixing that is not present.
  (These are why `corr(δ, R(r))` and `corr(max_bias, R(r))` are weakly negative: a frozen
  *end pair* on a well-mixing fence raises `max_bias` without raising `λ_std`.)

### 3.2 The asymptotic law (exact, on frozen-boundary ordinal-sum towers)

`tight3 = a‖(b<c)` is the extremal 1/3–2/3 gadget: `δ = 1/3` exactly, both incomparable
pairs biased to exactly 2/3. Its `m`-fold ordinal sum keeps `δ = 1/3`, freezes every pair at
2/3, and grows `n = 3m`. Every ordinal sum has `λ_std = 1` exactly (the across-block mode has
zero transport energy) — the decomposable endpoint — so the tower shows **how fast a single
global vector `r` chases the ceiling 1**:

```
 n      λ_std   R(r)     1−R(r)      E[inv_e]   (1−R(r))·n²   energy(r)=(8/9)·E[inv_e]
  6     1.000   0.9224   7.76e-2      1.33        2.79
  9     1.000   0.9686   3.14e-2      2.00        2.54
 12     1.000   0.9829   1.71e-2      2.67        2.46
 18     1.000   0.9926   7.44e-3      4.00        2.41
 24     1.000   0.9958   4.15e-3      5.33        2.39
 36     1.000   0.9982   1.84e-3      8.00        2.38   →  (1−R(r))·n² → 64/27 ≈ 2.37
```

Exact closed forms verified numerically on this tower:
```
energy(r) = (8/9)·E[inv_e]     (bounded ratio, no n-factor)
‖r‖²      → n³/12              (‖r‖²/n³ = 0.0329, 0.0707, …, 0.0830 → 1/12)
E[inv_e]  = 2n/9              (linear here — thin, because ordinal-sum)
⇒  1 − R(r) = energy(r)/‖r‖² = (32/3)·E[inv_e]/n³ = (64/27)/n² = Θ(1/n²).
```
Width-3 control `3AC^⊕m` (3-antichain ordinal sum): `R(r) = 1.000` **exactly** for all `n`
(there `r` *is* the dominant eigenvector by symmetry) — the perfect-certificate endpoint.

**The general law.** The tower is one instance of the exact identity
`1 − R(r) = energy(r)/‖r‖²`. Across the *whole* ensemble the two ingredients stay controlled:
`energy(r)/E[inv_e]` has median 1.6, p90 2.5, max 4.8 (**bounded, `O(1)`**), and the locality
ratio `E[Σdisp²]/E[inv_e]` (§4) has median 3.0, max 4.3, essentially flat in `n`
(`~ n^{0.12}`). So `1 − R(r) = O(E[inv_e]/n³)` is the operative bound generally, not just on
the tower.

---

## 4. STEP 3 — proof attempt, and the named wall

`1 − λ_std(P) ≤ 1 − R(r) = energy(r)/‖r‖²`. A proof of `frozen ⟹ λ_std → 1` via `r` reduces
to bounding the two factors. Both are **first-order, computable observables** of `r` — this
is the structural advantage over the prefix/LIB route, which needed the conclusion.

**Reduction.** Label by `e` so e-rank(`x`) = `x`. Then (program §4, Laplacian form)
```
energy(r) = ½ Σ_{i,j} a_{ij}(er_i − er_j)²,   a_{ij} = (N_{ij}+N_{ji})/(2|L|),
```
`N_{ij} = #{σ : position i holds the e-rank-j element}`. With `Λ = max_i (er_{i+1}−er_i)`,
```
energy(r) ≤ ½ Λ² · E_σ[ Σ_a (a − e-rank(σ(a)))² ]  =  ½ Λ² · E[Σdisp²].
```

**Lemma (A) — SPREAD:** frozen ⟹ `er` is monotone in `e` with `‖r‖² = Ω(n³)`.
- *Status:* this **is** the program's existing conjecture **L2** ("monotone standard mode /
  order identification"). Strongly supported here: `er_x ≈ x`, `‖r‖² → n³/12`,
  `expected_rank_monotone` holds across the ensemble. Not proven, but pre-existing and
  independent of this route.

**Lemma (B) — LOCALITY:** frozen ⟹ `E[Σdisp²] = O(E[inv_e])` and `Λ = O(1)`.
- *Status:* **new.** Empirically the ratio `E[Σdisp²]/E[inv_e]` is median 3.0, p90 3.6, max
  4.3 over the ensemble, and grows like `n^{0.12}` (i.e. **essentially flat**) — the worst
  cases are `n ≤ 9`, `δ = 0.5` posets (out of deep regime). Proven for near-ordinal-sums
  (displacements are within-block, `O(1)`). **Unproven, and untested at large-`n`
  genuinely-quadratic-`E[inv_e]`** — where an element could cross a whole frozen chain and
  contribute `Θ(n)` to a displacement, potentially blowing up `E[Σdisp²]/E[inv_e]`. **This is
  the honest wall.**

**Given (A) + (B):**
```
1 − λ_std ≤ 1 − R(r) = energy(r)/‖r‖² ≤ ½Λ²·E[Σdisp²] / Ω(n³)
          = O(E[inv_e]/n³)  =  O(1/n)   even when E[inv_e] = Θ(n²).
```
So the expected-rank route delivers `λ_std ≥ 1 − O(1/n)` (indeed `1 − O(1/(γn))`-type in the
thin case `E[inv_e]=O(n)`, matching the ticket's target), **without a thin prefix**, and
under two lemmas that are strictly weaker + non-circular than LIB.

**Why this is a *better* L1b than the prior route.**

| | prior route (mg-8b64, prefix/LIB) | this route (expected rank) |
|---|---|---|
| certifying object | prefix indicator `1_{A_k}` | single global smooth `r = T_P u` |
| what it needs | a **thin prefix** (`E[inv_e]=O(n)` = the conclusion) | spread (L2) + locality of `r` |
| circularity | near-circular (certifies hypothesis with conclusion) | non-circular (first-order observables) |
| tolerates quadratic `E[inv_e]` | **no** | **yes** (`1−λ_std=O(1/n)`) |
| empirical certificate quality | AMBER, needs `δ<1/3` global | capture 0.94, 0 false-neg on `λ≥0.9` |

---

## 5. Verdict, and honest caveats

**GREEN-in-regime / AMBER-as-proof.** The expected-rank vector is a strictly better L1b
certificate: a rigorous per-poset lower bound on `λ_std` from a single global smooth mode,
empirically capturing 94 % of the gap-to-1 and never failing on genuine bad mixing, with an
exact `1 − R(r) = Θ(E[inv_e]/n³)` scaling law that **avoids the thin-prefix bottleneck** (it
tolerates quadratic `E[inv_e]`). The proof reduces to two first-order lemmas that are weaker
and non-circular versus LIB.

**Caveats (the skeptical bar):**
1. **Not a proof.** Contingent on (A) spread [= program L2] and (B) locality [new, unproven].
2. **The clean `1/n²` rate is on ordinal-sum towers** (`λ_std = 1` exactly, decomposable
   endpoint). For genuine non-decomposable in-regime posets the evidence is the 0.94 capture
   and zero false-negatives, *not* a demonstrated rate — no true counterexamples exist to test
   the deep regime, and reachable non-decomposable frozen posets top out at `λ_std ≈ 0.96`
   (`n ≤ 9`).
3. **Locality (B) is the real risk.** It is only checked at `n ≤ 9` and mostly `δ = 0.5`; its
   behavior at large-`n` genuinely-quadratic-`E[inv_e]` frozen width-3 posets is exactly what
   the accessible ensemble cannot reach. A large-displacement frozen construction that breaks
   (B) would be the falsifier to hunt next.

**Suggested next step (not filed — recommendation only):** attempt lemma (B) directly —
bound `E[Σdisp²]` by `E[inv_e]` for width-3 frozen posets using the frozen structure to cap
single-element displacements (each element crosses `O(1)` frozen pairs in expectation), OR
search for a width-3 frozen construction with `E[Σdisp²]/E[inv_e]` growing in `n` (the
falsifier). Lemma (A) is already the program's L2 and can be pursued independently.

---

## 6. Reproduce

```
python3.11 scripts/onethird_mg8201_L1b_expected_rank_probe.py     # ~4 min; writes the JSON
# outputs: data/onethird-mg8201-L1b-expected-rank.json  (summary + 2529 rows)
```
Deterministic (b0a6 `_LCG`, no wall-clock/RNG). Requires numpy (python3.11 on this host).
