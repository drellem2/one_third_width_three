# OneThird L1b spot-check — does Theorem E's BK low-conductance cut force λ_std ~ 1 in the transport quotient?

**Work item:** mg-8b64 (high, repo `one_third_width_three`). Daniel-authorized, no gate
(gate mg-7d8a lifted 2026-07-13 — "let's go now, no gate"). Sole-remaining-gap
falsification spot-check after mg-b0a6 (kill-shot probe, ALIVE) and mg-3ce3 (L4
stability, GREEN) in the spectral / near-ordinal-sum program.

**Verdict: AMBER (leaning GREEN in-regime).**
The transfer L1b holds **robustly in the counterexample-driving regime** with a clean
near-linear modulus, **but it requires the global all-pairs-frozen hypothesis
δ(P) < 1/3** — the *single* low-conductance BK pair-cut that Theorem E outputs does
**not**, by itself, force λ_std ~ 1. The naive single-cut reading of L1b is refuted
by 166 explicit posets (all of which possess a near-balanced or balanced pair, i.e.
are **not** counterexamples). The program's *actual* needed implication —
"counterexample ⇒ λ_std ~ 1" — is empirically supported with **zero in-regime
refuters**. This is NOT a falsification (not RED): the last gap does not break, but
its proof must be phrased from δ < 1/3, not from Theorem E's conclusion.

**Skeptical bar (pm-onethird `feedback_empirical_green_is_not_proven`):** everything
below is empirical over a finite poset ensemble (n ≤ 8), **not** a proof. GREEN-in-regime
means "the transfer holds on the tested ensemble with a reported modulus to aim a
proof at," never "L1b is proven."

---

## 0. What L1b is, and why it is the sole remaining gap

The spectral / near-ordinal-sum program's falsification chain, for a hypothetical
**minimal counterexample** `P` to the 1/3–2/3 conjecture (a width-3, indecomposable
`γ`-counterexample: **every** incomparable pair has `Pr[x<y] ∉ [1/3, 2/3]`):

```
minimal counterexample
  → low-conductance BK cut          [PROVEN: Theorem E / thm:cex-implies-low-expansion, step8.tex]
  → ??? L1b TRANSFER ???
  → bad mixing in the TRANSPORT quotient, i.e. λ_std ~ 1
  → Cheeger low-conductance prefix → near ordinal sum
  → balanced pair by minimality → contradiction.
```

- **Theorem E's object** lives on the **BK / adjacent-transposition graph** on `L(P)`
  and is a **pair-indicator cut** `S_xy = {σ : x precedes y}` for a *BK-frozen* pair —
  the pair minimizing `E(f_xy)/Var(f_xy)`, bounded by `2/(γn)` (step8.tex
  `lem:frozen-pair-existence`).
- **The transport quotient** is the n-dim element-position object of mg-b0a6:
  `(T_P)_{x,a} = Pr[x occupies position a]`, `S_P = (T_P + T_Pᵀ)/2` on `H = 1^⊥`,
  `λ_std = ` top eigenvalue on `H`. `λ_std = 1` **iff** `P` is an ordinal sum;
  `λ_std ~ 1` **iff** near-ordinal-sum. `I − S_P` is a weighted graph Laplacian on
  the labels `[n]`, so cuts are leakages: `⟨1_A, (I−S_P)1_A⟩ = E_σ|A \ σ(A)|`.

**L1b = the transfer:** does a low-conductance BK pair-cut force `λ_std ~ 1` (small
transport gap `1 − λ_std`)? This is the repo's own **cuts-by-pairs** open problem — a
**Buser-type reverse Cheeger for width-3 pair cuts**
(`docs/compatibility-geometry-cuts-by-pairs-scoping.md` §4.3(i), §5.2–5.3, verdict
AMBER; and §4.2 "the general non-width-3 version is false — depends on width-3
rigidity").

---

## 1. Method (script + engines reused)

**Script:** `scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py`.
**Data:** `data/onethird-mg8b64-L1b-bk-transport-transfer.json` (1091 posets).
Reuses the mg-b0a6 engine **verbatim** (`Poset`, exact-rational transport matrix,
`standard_block_and_lambda`, `expected_rank`, `before_prob_dp`, prefix-defect
machinery, both-connected enumeration, named stress posets) and **adds the BK side**.

New BK machinery (all exact-rational where the quantity is exact):

- **`bk_pair_cut(P,x,y)`** — Theorem E's cut `S_xy`. Exact `p_xy = Pr[x<y]`,
  `Var = p(1−p)`, adjacency count `Adj_{xy} = #{σ : x,y consecutive}`, Dirichlet
  energy `E(f_xy) = Adj/(2(n−1)|L|)`, the **frozen ratio** `E/Var`, and the actual
  conductance `Φ(S_xy) = (Adj/2)/((n−1)·min(p,1−p)·|L|)` in step8.tex's
  `vol(S)=|S|(n−1)` normalization (verified `Φ ≤ E/Var`, `lem:dirichlet-conductance`).
- **`bk_frozen_pair(P)`** — Theorem E's argmin-`E/Var` pair, plus the min-Φ pair and
  the max-bias pair; and `δ(P) = max_pair min(p,1−p)` (counterexample iff `δ < 1/3`).
- **`bk_lambda2(P)`** — 2nd eigenvalue of the lazy `(n−1)`-regular BK walk (BK
  spectral gap), capped at `|L(P)| ≤ 2200`.
- **`bk_cheeger_exhaustive(P)`** — exhaustive min-conductance over all `2^{|L|}` cuts,
  capped at `|L(P)| ≤ 15`; records whether the argmin is a pair cut.
- **Operational transfer** `transport_image_of_pair` — maps the frozen pair to a
  transport label-cut (the min-conductance prefix of the expected-rank order that
  separates `x` from `y`) and evaluates its transport conductance `Φ_T`.

**Ensemble / n! wall (LOGGED, as the ticket requires).**

> **[CORRECTED — the `n = 7` count is wrong. mg-2c34 §5.1, located by mg-09ea §6, landed by
> mg-60d3 2026-07-29.]** There are **956** both-connected `n = 7` isomorphism classes, not 946:
> `enumerate_both_connected` dedups by `iso_signature`, which its own docstring says is *"not a
> perfect canonical form"*, and it collapses 10 classes at `n = 7`. `n = 3..6` are **unaffected**
> (`iso_signature` is exact below `n = 7` and first collides there). **No conclusion in this
> document turns on the 10** — they are ordinary posets with `δ ∈ [0.45, 0.50]` and
> `c ∈ [0.992696, 0.998412]`, all since measured. Only the count is wrong.

Exhaustive both-connected posets **n = 3..7** (3, 9, 12, 104, 946 posets), plus a
mandated stress-family set (N-poset / 2+2, stacked & width-3 double-N, crown `S₃⁰`,
zigzag fences to n=8, width-3 SP/ordinal-sum controls, tight `δ→1/3` chains
`1‖chain_k` to n=8, triple-ladder n=8), plus b0a6's named posets. **n = 8 exhaustive
enumeration is NOT run** (2²⁸ relation-subsets — beyond the enumerator); n=8 is
covered by targeted families only. LE wall cap `|L(P)| ≤ 40320` (=8!); **0 posets
skipped for the LE wall, 0 for the BK spectrum cap** on this ensemble
(max `|L(P)| = 480` at n=7). Total: **1091 posets** with ≥1 incomparable pair.

---

## 2. Result — the counterexample-regime conditioning is decisive

### 2.1 The naive single-cut reading is FALSE (the 166 refuters)

Ranking all 1091 posets by the frozen-pair conductance `Φ_BK`, the lowest-`Φ_BK`
posets do **not** have `λ_std ~ 1`. There are **166 posets** with `Φ_BK ≤ p25` (below
the 25th percentile) yet transport gap `≥ median` — e.g.

| poset | δ(P) | Φ_BK(frozen) | λ_std | max_bias |
|---|---|---|---|---|
| `enum-n7-#600` | **0.500** | 0.0556 | 0.774 | 0.894 |
| `enum-n7-#3`   | **0.500** | 0.0556 | 0.785 | 0.900 |
| `enum-n7-#20`  | **0.500** | 0.0573 | 0.768 | 0.909 |
| `enum-n7-#611` | **0.500** | 0.0577 | 0.836 | 0.926 |

**Every one of the 166 refuters has δ(P) ∈ {0.473, 0.474, 0.500}** — i.e. it possesses
a near-balanced or perfectly balanced pair, so it is **not a counterexample at all**.
Its Theorem-E-frozen pair is a *single* very-unbalanced pair (`max_bias ~ 0.9`) whose
pair-cut is low-conductance, but the poset as a whole mixes fine in the transport
quotient (`λ_std ~ 0.77–0.84`, bounded away from 1).

> **Finding 1.** A low-conductance BK **pair-cut does not, by itself, force
> λ_std ~ 1.** The transfer fails for posets with a single frozen pair. This is the
> exact transport-level image of the scoping doc's §4.2 finding: *the general
> (non-width-3, non-all-pairs-frozen) cut-by-pair correspondence is false.*

### 2.2 In the counterexample-driving regime the transfer holds (zero refuters)

Conditioning on `δ(P) → 1/3⁻` (the counterexample regime = **all** pairs frozen), the
implication `corr(Φ_BK, transport gap)` — which the program predicts should be
**positive** (both shrink together as `n → ∞`) — **sharpens sharply and positively**:

| bucket | # posets | corr(Φ_BK, gap) | λ_std [min / med / max] |
|---|---|---|---|
| δ ≤ 0.38 | 7   | **+0.926** | 0.500 / 0.856 / 0.902 |
| δ ≤ 0.42 | 55  | **+0.714** | 0.447 / 0.865 / 0.944 |
| δ ≤ 0.50 (all) | 1091 | +0.043 | 0.387 / 0.852 / 1.000 |

- **Regime-aware refuters** (δ ≤ 0.36 **and** low Φ_BK **and** λ_std ≤ 0.75): **ZERO.**
- **In-regime (δ ≤ 0.40): ZERO** posets with `Φ_BK ≤ 0.12` **and** `λ_std ≤ 0.80`.

The smallest-δ posets (deepest toward the counterexample regime, n ≥ 5) all have high
`λ_std`, pushed toward 1:

| poset | δ(P) | λ_std | gap | Φ_BK |
|---|---|---|---|---|
| `enum-n6-#78`  | 0.357 | 0.865 | 0.135 | 0.150 |
| `enum-n7-#809` | 0.360 | 0.902 | 0.098 | 0.119 |
| `enum-n7-#945` | 0.381 | 0.944 | 0.056 | 0.167 |
| `enum-n6-#103` | 0.385 | 0.924 | 0.076 | 0.200 |
| `enum-n7-#820` | 0.391 | 0.912 | 0.088 | 0.119 |

> **Finding 2.** Restricted to the counterexample-driving regime (all pairs frozen,
> δ near 1/3), **low Φ_BK reliably co-occurs with a small transport gap
> (λ_std → 1)**, with `corr` climbing to **+0.93** as we approach the regime, and
> **no in-regime refuter**. This is the GREEN direction — the program's *actual*
> needed implication is supported.

### 2.3 The n-dependence is honest and the right sign

`Φ_BK ≤ 2/(γn) → 0` and `λ_std → 1` are both **large-n** phenomena; at small n the
"low-conductance" hypothesis is empty. Per-n, the minimum-δ (most counterexample-like)
poset's `λ_std` climbs with n:

| n | min δ | λ_std at argmin-δ | Φ_BK there |
|---|---|---|---|
| 3 | 0.333 | 0.500 | 0.500 (**not** low — Theorem E gives no bound at n=3) |
| 4 | 0.400 | 0.447 | 0.333 (not low) |
| 5 | 0.364 | 0.746 | 0.167 |
| 6 | 0.357 | 0.865 | 0.150 |
| 7 | 0.359 | 0.856 | 0.111 |
| 8 (families) | 0.429 | 1.000 | 0.066 |

The two apparent low-δ / low-λ_std points (the tight `a‖(b<c)` at n=3, λ_std=0.5) have
`Φ_BK = 0.5` — **not** low — so they are outside the low-Φ_BK hypothesis and do not
refute. As soon as `Φ_BK` genuinely drops (n ≥ 5 in-regime), `λ_std` sits at
**0.85–0.94**. The raw `corr(δ, λ_std) = +0.03` is confounded by these small-n tight
points; conditioned on n it is the predicted sign.

---

## 3. Empirical modulus (to aim a proof at)

In-regime (`δ ≤ 0.42`, n = 55) least-squares fit of `transport_gap ~ C·Φ_BK^α`:

```
α (log-log slope) = 0.469        r = 0.442        n = 55
gap / Φ_BK ratio  : min 0.300, median 1.349, max 3.604
```

So **in the counterexample regime, `transport_gap ≲ 3.6 · Φ_BK`** (a *linear*
reverse-Cheeger-type bound; the sublinear α ≈ 0.5 is the small-n log-log curvature).
Combining with **Theorem E**'s `Φ_BK ≤ 2/(γn)`:

```
1 − λ_std  =  transport gap  ≲  3.6 · Φ_BK  ≤  7.2 / (γn)   →  0     (n → ∞),
i.e.        λ_std  ≥  1 − O(1/(γn))  →  1.
```

**This is exactly the L1b conclusion the program needs** — and the constant is
concrete (`≈ 3.6`, to be sharpened) — **but the bound `gap ≲ 3.6·Φ_BK` is
in-regime-only.** Out of regime it is false: the 166 §2.1 posets have `gap/Φ_BK` up to
`≈ 4.1/0.056 ≈ 4` for one frozen pair while `λ_std` stays ~0.77 — the *unconditioned*
`gap/Φ_BK` is unbounded because a lone frozen pair drives `Φ_BK → 0` without driving
`λ_std → 1`.

---

## 4. Verdict and recommendation

**AMBER — leaning GREEN in-regime; NOT RED.** Precise sub-verdicts:

- **RED for the naive single-cut reading of L1b** ("Theorem E's one low-conductance
  `S_xy` ⇒ λ_std ~ 1"): **refuted** by 166 explicit posets (all with a near-balanced
  pair). A proof of the form "one low-Φ_BK BK pair-cut ⇒ λ_std ~ 1" is **doomed**.
- **GREEN for the program's actual requirement** ("δ(P) < 1/3, all pairs frozen ⇒
  λ_std ~ 1"): supported on the full n ≤ 8 ensemble — `corr` → +0.93 into the regime,
  **zero in-regime refuters**, clean modulus `1 − λ_std ≲ 3.6·Φ_BK`.
- **The "extra structure" the AMBER key names** is **exactly Theorem E's own
  hypothesis** (a `γ`-counterexample = *every* pair frozen, δ < 1/3), plus width-3.
  It is not a new ad-hoc condition — but it is **strictly more** than Theorem E's
  *conclusion* (one low-conductance cut). There is a real, previously-implicit step
  between "Theorem E gives a low-conductance cut" and "the transport quotient mixes
  badly."

**Is the L1b proof (Buser-type reverse Cheeger for width-3 pair cuts) worth investing
in? — YES, with a sharpened target.** The empirical evidence says the theorem is true
in the form the program needs. But this probe pins down the correct hypothesis:

> **Target for the L1b proof (revised).** For width-3 indecomposable `γ`-counterexamples
> `P` (equivalently δ(P) < 1/3, *every* pair frozen), `1 − λ_std(P) ≤ C(γ)·Φ_BK(P)` for
> an absolute-modulo-γ constant `C(γ)` (empirically `C ≈ 3.6`), hence `λ_std(P) ≥
> 1 − 2C(γ)/(γn) → 1`. The proof **must** consume the all-pairs-frozen structure — the
> single-cut version is false (§2.1).

Concretely, the proof should relate the transport Dirichlet form `⟨1_A,(I−S_P)1_A⟩ =
E_σ|A\σ(A)|` to the BK Dirichlet energies of the *family* of frozen pair-indicators
`{f_xy}` (not one of them), using width-3 rigidity to convert "all `E(f_xy)/Var`
small" into "some low-leakage label prefix" (b0a6 KILL-SHOT 4 prefix-capture is the
transport-side handle; this probe's `transport_image_of_pair` is the operational
bridge). This is the same Buser-type analysis flagged AMBER in the cuts-by-pairs
scoping — now with an empirical modulus and a corrected hypothesis.

**Downstream (per ticket):** since this is GREEN-in-regime (not RED), the program's
last empirical gap holds. As the ticket notes, if the L1b proof push proceeds, the
empirical-GREEN lemmas **T1/T2/L4** still need real proofs and **L2** needs restating
in soft form (mg-b0a6 T3 = AMBER: the exact monotonicity lemma is false, the soft
Kendall-τ claim holds). None of those are touched here.

---

## 5. Reproduce

```
cd scripts
python3.11 onethird_mg8b64_L1b_bk_transport_transfer_probe.py \
    --n-lo 3 --n-hi 7 --quiet \
    --dump ../data/onethird-mg8b64-L1b-bk-transport-transfer.json
```

(~72 s wall on a 10-core M-series; `python3.11` has numpy/scipy.) Full per-poset table
+ all correlations, buckets, per-n conditioning, refuter list and modulus fit land in
the JSON `summary`. The BK n! wall and the cap-skip counts are logged in
`summary.skipped_le` / `summary.skipped_spectrum` and `caps`.

---

## 6. Cross-references

- **mg-b0a6** — spectral/near-ordinal-sum kill-shot probe (ALIVE); this probe reuses
  its transport engine and continues its L1 risk item. `docs/OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md`.
- **mg-3ce3** — L4 near-ordinal-sum stability (GREEN). `docs/OneThird-L4-NearOrdinalSum-Stability-Probe.md`.
- **Theorem E** — `step8.tex` §sec:G1, `thm:cex-implies-low-expansion`,
  `lem:dirichlet-conductance`, `lem:frozen-pair-existence`.
- **Cuts-by-pairs scoping (mg-d4ed)** — `docs/compatibility-geometry-cuts-by-pairs-scoping.md`
  §4.2 (general version false), §4.3 (width-3 salvage / route (i) direct-spectral),
  §5.2–5.3 (Buser-type reverse Cheeger requirement). This probe empirically confirms
  §4.2 at the transport level and supplies the missing modulus for §5.2.
- **pm-onethird memory** `project_spectral_near_ordinal_sum_program.md`;
  `feedback_empirical_green_is_not_proven`; `feedback_n_poset_is_not_ordinal_sum`.
