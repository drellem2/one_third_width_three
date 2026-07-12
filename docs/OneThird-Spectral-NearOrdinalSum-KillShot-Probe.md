# OneThird — Spectral / Near-Ordinal-Sum Programme: Falsification Kill-Shot Probe

**Work item.** `mg-b0a6` (high, repo `one_third_width_three`).
**Authorization.** Daniel, live 2026-07-12 ("Go for it") — supersedes the
one-third build-pause gate for THIS compute-only probe.
**Source programme.** `spectral_near_ordinal_sum_program.tex` (Daniel,
2026-07-12); PM review in pm-onethird memory
`project_spectral_near_ordinal_sum_program.md`.
**Script.** `scripts/onethird_mgb0a6_spectral_killshot_probe.py`
(pure-Python exact linear-extension engines + numpy eigenvalues).
**Data.** `data/onethird-mgb0a6-spectral-killshot.json` (126-poset table + aggregates).

---

## Executive verdict

| Kill-shot | Claim tested | Verdict |
|---|---|---|
| **1. Distinguished-order existence** | the >2/3 strong-majority orientation ∪ poset is acyclic (a distinguished order `e` exists) | **GREEN** (well-stressed) |
| **2. Standard dominance** | the full symmetrized Cayley-walk's 2nd eigenvalue = λ_std (gap lives in the standard sector) | **GREEN** |
| **3. Monotonicity (L2)** | dominant standard eigenvector monotone along `<_P` and in the expected-rank order | **AMBER** |
| **4. Prefix capture / near ordinal sum (L4/L3)** | a threshold sweep yields a genuine prefix capturing λ_std **and that prefix is a thin interface** | **AMBER** |

**Overall call: the programme is ALIVE — no kill-shot fired RED.**
Both cheap foundational gates (1, 2) pass cleanly; the two proof-lemma
predictions (3, 4) are qualitatively supported but the *exact* lemmas a proof
needs are not delivered, and the probe localizes the surviving risk precisely.

**This is a conditional green light to harden, NOT a claim the hard part is
done.** Per the skeptical bar (pm-onethird `feedback_lean_no_vacuous_baseline_proofs`,
`feedback_audit_bar_for_axioms`): a Rayleigh quotient above 1/3, or a prefix that
captures 95% of λ_std, is **not** evidence of near-ordinal-sum structure. The
decisive quantity is the interface leakage Δ₁, and the probe shows the leakage is
governed by λ_std → 1, which is exactly the **borrowed, unproven** BK-bad-mixing
input (L1). See "Where the risk actually lives".

---

## Method & test set

For a poset `P` on `[n]`, LE(P) = its linear extensions (one-line notation:
σ(a) = element at position a).

- **Element-position transport** `(T_P)_{x,a} = Pr_{σ∈LE(P)}[σ(a)=x]`, doubly
  stochastic. **Standard block** `S_P = (T_P+T_Pᵀ)/2` restricted to `H = 1⊥`;
  `λ_std(P)` = top eigenvalue of `S_P` on `H`. `I − S_P` is a weighted graph
  Laplacian on `[n]` (transport-energy identity), so cuts are leakages:
  `⟨1_A,(I−S_P)1_A⟩ = E_σ|A∖σ(A)|`.
- **Test set.** All posets whose comparability AND incomparability graphs are
  both connected (the "irreducible under disjoint-union and ordinal-sum" core),
  **exhaustively** for `n = 3..7` (test 1) and `n = 3..6` (tests 2–4: 126
  posets), **plus** the mandated named stress cases — the tight δ≈1/3 posets and
  the **N-poset family** (2+2 = {x₁<y₁, x₂<y₂}, which is *not* an ordinal sum and
  has nontrivial defect at every cut — pm-onethird
  `feedback_n_poset_is_not_ordinal_sum`).
- **Two independent exact engines** (order-ideal DP over LE-counts; brute force
  over permutations) cross-check every rational quantity. Validation this run:
  847 pairwise before-probabilities agree DP-vs-brute with **0 mismatches**; the
  full Cayley-walk top eigenvalue = 1.0 exactly (trivial rep); the full-walk 2nd
  eigenvalue equals the independently-built n×n standard block λ_std to ~1e-15
  (confirms the representation-theory identity `S_P = ρ_std(η_P)`).

**Compute boundary (honest).** Full n!×n! Cayley spectra: exhaustive `n≤6`,
spot-checked `n=7` (top-6 highest-λ posets). Distinguished-order test:
exhaustive `n≤7` + 36 000 reproducible random samples at `n=8,9,10`. **No poset
in reach is an actual counterexample** (δ<1/3 requires n well beyond exhaustive
range; the conjecture is verified for all these n). Every conjecture the .tex
states "for a minimal counterexample" is therefore tested on the accessible
proxy — small posets, especially the highest-λ_std ones nearest the "bad-mixing"
regime — not on a real counterexample. This limit is intrinsic and is flagged at
each test.

---

## Kill-shot 1 — Distinguished-order existence — **GREEN (well-stressed)**

*Refutes nothing; supports the .tex's unstated foundational assumption (it sits
before L1–L4).* The .tex assumes a minimal counterexample can be labelled by a
total order `e` agreeing with all >2/3 majority orientations. Linear-extension
**majority** relations cycle in general (Fishburn); if the >2/3-**strong**
version cycles on any P, the programme never starts.

- **Exhaustive n≤7:** across **1063** both-connected posets, the >2/3-strong
  orientation ∪ poset is **acyclic on every one**. Notably the weaker >1/2
  (Fishburn) majority orientation **also never cycles at n≤7** — so at these
  sizes the test is intrinsically unstressed.
- **Reproducible large-n stress scan** (LCG-seeded, 36 000 samples over
  n=8,9,10): exactly **one** poset produces a genuine >1/2-majority 3-cycle
  (n=10, seed 2589: a `0→3→2→0` cycle among incomparable-pair majority
  preferences). **On that very poset the >2/3-strong orientation is still
  acyclic** — the strong threshold drops the three near-balanced (½<p<⅔) edges
  that form the cycle. Recorded as `LEM_CYCLIC_WITNESS_N10` in the script.

**Reading.** The Fishburn pathology is real (witnessed), but the >2/3 threshold —
the one the programme actually invokes — defeats it in every case tested. This is
positive evidence for the distinguished-order assumption. **Residual caveat:** a
true counterexample has δ<1/3, i.e. *every* incomparable pair is >2/3-oriented (a
*total* strong tournament); we cannot exhibit one, so total-tournament acyclicity
is supported by analogy, not proven.

---

## Kill-shot 2 — Standard dominance — **GREEN**

*Supports the "Standard dominance" conjecture (§8 of the .tex).* The .tex warns
this is "not automatic for a Cayley graph."

- Full symmetrized Cayley spectrum computed exhaustively for all **126**
  both-connected posets `n≤6`: the 2nd-largest eigenvalue equals λ_std in **every
  case** (excess ≤ ~1e-15). Spot-checked at `n=7` on the six highest-λ_std
  both-connected posets (λ_std up to 0.9593): **0 failures**, excess ≈ machine-ε.
- Representation theory explains and corroborates this: λ_std is *exactly* the
  standard-irrep block of the convolution operator, so it is always present; a
  failure would require some non-standard irrep to out-eigenvalue it, which never
  occurred.

**Reading.** The spectral gap of the walk genuinely lives in the low-dimensional
transport quotient. This is the cleanest GREEN of the four and is the reason the
whole "n-state quotient" reduction is not vacuous.

---

## Kill-shot 3 — Monotonicity (L2) — **AMBER**

*Two sub-claims, opposite outcomes.*

**(a) Soft claim — "expected rank largely determines the eigenvector ordering"
(.tex §12): SUPPORTED.** Kendall-τ between the dominant eigenvector's coordinate
order and the expected-rank order: **median 0.857, mean 0.842** (min 0.286, max
1.0) over 126 posets. "Largely" is fair.

**(b) Exact lemmas — monotone standard mode / order identification: FALSE.**

- *Monotone along `<_P`* (`x<_P y ⟹ v_x ≤ v_y`): holds for **124/126** posets,
  but **2 genuine violations** at n=6 — and they are **not** degeneracy
  artifacts (top-of-H spectral gaps 0.45 and 0.31) and occur at the **two
  highest λ_std in the whole set** (0.9239, 0.9256), i.e. *exactly* the near-1
  "bad-mixing" regime the programme cares about. The eigenvector is genuinely
  non-monotone there.
- *Exact order identification* (eigenvector order = expected-rank order): fails
  on **85/126** posets. All 100 inversions are genuine (0 are expected-rank
  ties); magnitudes are not negligible (ΔE[pos] up to 1.5 positions, median 0.47).

**Reading — why AMBER not RED.** The programme's Step 3 needs monotonicity *or* a
direct low-conductance prefix, and the prefix conclusion survives regardless (see
kill-shot 4: the best cut is always a prefix, capture ≈0.99, even at the two
non-monotone posets). So the literal monotonicity lemma L2 is **false as a
universal statement** and will need a hypothesis restriction, but the *thing L2
is invoked to produce* (a prefix cut) is delivered by other means. L2 is not
dead; it is mis-stated.

---

## Kill-shot 4 — Prefix capture / near ordinal sum (L4/L3) — **AMBER**

This is where the skeptical bar bites hardest and where the programme's real work
lives.

**Literal prefix metrics — GREEN:**

- **The globally-optimal cut is ALWAYS an expected-rank prefix.**
  `best_cut_Rayleigh − best_prefix_Rayleigh ≤ 3.3e-16` (machine zero) across all
  126 posets; the eigenvector threshold-sweep optimum is a prefix (or suffix) of
  `e` in **125/126** cases. So the prefix restriction (L3) costs nothing.
- **Prefix capture fraction** `best_prefix_R / λ_std`: **median 0.951, mean
  0.934** (min 0.447). A single prefix indicator recovers ~95% of the standard
  eigenvalue's energy — "constant fraction" (.tex "Prefix capture" conjecture) is
  supported; "1−o(1)" is not uniform (the min is below ½).

**Near-ordinal-sum step (the actual L4 goal) — the caution:**

The programme's chain is prefix ⟹ **near ordinal sum** = *thin interface*, i.e.
small leakage `Δ₁(A) = E|A∖σ(A)| / min(|A|,|Aᶜ|)`. A high Rayleigh quotient is
**not** that (explicit .tex "Caution" + the skeptical bar). The probe separates
the two:

- **λ_std → 1 does drive thinness:** Pearson correlation between `(1−λ_std)` and
  the thinnest available prefix `min_k Δ₁` is **+0.776**. The five highest-λ_std
  n=6 posets (λ≈0.94) have `min Δ₁ ≈ 0.033`, Δ₀ ≈ 0.10 (thin); the high-λ band
  (λ≥0.85, 54 posets) has `min Δ₁` median 0.081, max 0.167.
- **But the prefix the *spectrum* picks is not always the thin one, and no small
  poset achieves a genuinely thin interface.** `best_prefix_Δ₁` ranges up to
  **0.5** (a maximally fat interface); even `min Δ₁` over *all* cuts has median
  0.119 and never drops to 0 for a non-decomposable poset in range. Because
  λ_std tops out at ~0.94–0.96 at n≤7 (nowhere near 1), the "Δ₁ → 0" limit the
  proof needs is **not reachable** in the accessible range — only the *trend* is.

### The N-poset: the skeptical-bar centrepiece

The mandated stress case (2+2 = {0<1, 2<3}) makes the point concretely. It
**passes kill-shots 1–3 with a clean bill of health** yet **fails the L4 goal**:

| quantity | N-poset value |
|---|---|
| λ_std | 0.539 |
| eigenvector monotone along `<_P` | **yes** |
| Kendall-τ (v vs E[pos]) | **1.000** (perfect order agreement) |
| standard dominance | **holds** |
| best-Rayleigh-prefix Δ₁ | **0.500** (maximally fat interface) |
| thinnest available cut `min Δ₁` | 0.167 (Δ₀ = 0.333: a third of extensions are non-concatenations) |
| prefix capture fraction | 0.618 |

So the spectral/prefix machinery hands the N-poset a "good" prefix (monotone
eigenvector, best-cut-is-a-prefix) whose interface is **as fat as possible**. The
prefix construction, *on its own*, does **not** certify near-ordinal-sum
structure — it is a faithful readout of λ_std, and thinness only appears when
λ_std is independently near 1. This is exactly the memory's warning
(`feedback_n_poset_is_not_ordinal_sum`: nontrivial defect at every cut) realized
numerically, and it is the precise obstruction any L4 stability lemma must
overcome. The N-poset is not a *counterexample to the correlation* (its λ is only
moderate, so it is "allowed" a fat interface) — it is a demonstration that the
prefix machinery is not the source of thinness.

---

## Where the risk actually lives (post-probe)

The chain `bad mixing ⟹ λ_std≈1 ⟹ low-conductance prefix ⟹ near ordinal sum ⟹
balanced pair` survives the probe, and the probe reassigns the risk:

1. **L1 (porting: bad BK mixing ⟹ λ_std ≥ 1−ε) is the load-bearing gap — and it
   is borrowed.** Everything downstream (standard dominance ✓, prefix = best-cut
   ✓, λ↔thinness trend ✓) behaves as the .tex hopes *conditional on λ_std
   actually reaching near 1*. The probe cannot manufacture λ≈1 at small n, and
   the near-ordinal-sum limit is entirely downstream of it. Per PM review, L1's
   BK-bad-mixing input for minimal counterexamples is **the same open crux the
   Čech/F-series cohomology program is chasing** — so this program does not
   reduce the hard input, it re-consumes it. **Deciding whether "BK bad-mixing
   for minimal counterexamples" is itself the real target (with both programs as
   downstream consumers) is the highest-value next question.**
2. **L4 (near-ordinal-sum stability) must beat the N-poset regime.** Even granting
   λ≈1, the stability lemma has to convert a thin-but-nonzero interface into a
   surviving balanced pair on one side, and the N-poset shows the interface is
   genuinely two-sided (Δ₀ = ⅓ at its best cut) — the "decomposable case" never
   absorbs it. The .tex offers a tool list, not a mechanism; this is unchanged by
   the probe.
3. **L2 (monotonicity) needs restating,** not proving as stated: it is false at
   the highest-λ posets, but its downstream product (a prefix cut) is supplied by
   the best-cut-is-a-prefix fact, so it is a cosmetic gap, not a structural one.

---

## Is the programme alive? — Yes, conditionally; hardening is warranted but not de-risked

- **No cheap refutation exists.** The two gates that could have killed the
  programme for almost no compute — a cyclic strong-majority tournament (no
  distinguished order) or a standard-dominance failure (the gap not in the
  quotient) — both held across exhaustive small posets and a large stress scan.
- **The structural readouts behave as predicted:** standard dominance is
  universal, the eigenvector order tracks expected rank (τ≈0.85), the best cut is
  always a prefix, and λ_std→1 correlates (+0.78) with a thinning interface.
- **The hard lemmas remain exactly as hard as flagged.** The probe did its job —
  viability-before-hardening — and returns a **GREEN-to-proceed-conditionally**
  with the surviving risk localized to L1 (borrowed BK bad-mixing) and L4
  (N-poset-proof stability). It does **not** license a claim that a Rayleigh/λ_std
  signal is near-ordinal-sum evidence; that inference is explicitly unsupported
  here.

**Recommended next step (not executed — probe scope only):** before any L2/L3/L4
proof push, resolve the L1 question at the *programme* level — is BK bad-mixing
for minimal counterexamples provable, and if so, port it to λ_std ≥ 1−ε — since
both this program and the Čech/F-series attack stall on that identical input. A
positive L1 makes tests 2–4's already-GREEN-trend machinery worth formalizing; a
negative or absent L1 leaves this program a faithful-but-idle quotient.

---

## Reproduction

```
# venv with numpy/scipy (no repo dependency); pure-Python exact engines otherwise
python scripts/onethird_mgb0a6_spectral_killshot_probe.py --t1-hi 7          # kill-shot 1 + LEM stress scan
python scripts/onethird_mgb0a6_spectral_killshot_probe.py --spectrum-hi 6    # kill-shots 1..4 battery
python scripts/onethird_mgb0a6_spectral_killshot_probe.py --dump             # data/ table + aggregates
```

All randomness is a seeded LCG (no clock/`Math.random`); results are bit-reproducible.

## Data appendix

Full 126-poset table + aggregates: `data/onethird-mgb0a6-spectral-killshot.json`.
Aggregates this run:

| metric | value |
|---|---|
| standard-dominance failures (n≤6 exhaustive + n=7 top-λ spot) | 0 / 132 |
| poset-monotone posets | 124 / 126 |
| Kendall-τ(v, E[pos]) median / mean / min | 0.857 / 0.842 / 0.286 |
| exact eigenvector-order = expected-rank-order | 41 / 126 |
| best-cut-is-a-prefix | 125 / 126 |
| prefix-capture fraction median / min | 0.951 / 0.447 |
| prefix-vs-best-cut gap (max) | 3.3e-16 |
| corr( 1−λ_std , min Δ₁ ) | +0.776 |
| min Δ₁ (high-λ band λ≥0.85) median / max | 0.081 / 0.167 |
| best-prefix Δ₁ (max, over all posets) | 0.500 (N-poset) |
| LEM (>1/2) cycles found n≤7 exhaustive / n=8-10 sampled (36k) | 0 / 1 |
| >2/3-strong cycles found (all tests) | 0 |
