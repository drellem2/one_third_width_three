# OneThird — L4 Near-Ordinal-Sum **Stability** Probe (thin interface, larger n)

**Work item.** `mg-3ce3` (high, repo `one_third_width_three`).
**Authorization.** Daniel, direct 2026-07-12 ("Scope") — supersedes the
one-third build-pause gate for THIS computational probe only.
**Predecessor.** `mg-b0a6` (spectral / near-ordinal-sum kill-shot probe;
`docs/OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md`,
`scripts/onethird_mgb0a6_spectral_killshot_probe.py`).
**Script.** `scripts/onethird_mg3ce3_L4_near_ordinal_stability_probe.py`
(reuses the b0a6 exact-LE order-ideal DP; adds an order-ideal DP **transport
matrix** so the probe is not bounded by the n! wall).
**Data.** `data/onethird-mg3ce3-L4-near-ordinal-stability.json`
(6929 posets, 6681 stability points, n up to **16**).

---

## Executive verdict

> **GREEN — near-ordinal-sum stability survives the thin-interface stress test.**
> The one surviving compute-testable risk from b0a6 (L4) does **not** fire. In the
> regime b0a6 could not reach — **small** interface leakage `ε = Δ₁` at **large n**
> (up to 16), including `λ_std` up to **0.996** (deep in the "bad-mixing" band) — a
> balanced pair survives on **every** tested poset in the form the minimal-
> counterexample endgame actually needs.

| Reading of "near-ordinal-sum stability" | Result |
|---|---|
| **Endgame form** (≥1 side keeps a within-side balanced pair in `P`) — *what the minimal-counterexample argument needs* | **GREEN — universal**: `1.0000` over **6681** both-non-chain posets; **0** RED events |
| **Stricter smaller-side-only form** (note Sec. 13 emphasis) | **AMBER refinement**: uniform for `ε < 0.085`; `89` losses above that, **every one covered by the bigger side** |
| Empirical modulus `F(ε)` (within-side probability drift) | `F(0.02) ≤ 0.073`, `F(0.05) ≤ 0.198`, `F(0.10) ≤ 0.346` (envelope) |

**This upgrades b0a6's L4 from "AMBER, untested in the thin regime" to
"GREEN in the endgame form, with a precisely-characterised smaller-side
non-uniformity."** It is *not* a proof and does *not* relax the skeptical bar:
`λ_std → 1` remains borrowed (L1), and this probe only tests the stability step
*given* a thin interface.

---

## What b0a6 left open, and why it needed larger n

b0a6 localized the programme's surviving risk to **L4**:

> low-conductance prefix ⟹ near ordinal sum ⟹ a balanced pair survives by minimality.

b0a6 was exhaustive at `n ≤ 6`, where **no thin interface occurs**: its best cuts
had `Δ₁` bottoming out ≈ 0.03–0.12, and the mandated **N-poset** (`2+2`) had a
*maximally fat* interface (`Δ₁ = 0.5`) — the **safe-to-Cheeger** case (a fat
interface is not what a `λ_std ≈ 1` sweep selects). The **dangerous, untested**
case is a genuinely **thin** interface (`Δ₁ → 0`): does thinness actually **force**
a surviving balanced pair? That is the near-ordinal-sum **stability** conjecture
(note Sec. 13), and it lives at larger `n`, which b0a6 could not reach because it
enumerated all `n!` linear extensions.

**Scaling fix (the ticket's scoping insight).** The L4 question needs only the
transport marginals `T_P` (`n×n`) and pairwise biases `p_xy = Pr[x before y]` —
both computable from **linear-extension marginals** via the order-ideal DP. It
does **not** need the `n!`-dim symmetrized Cayley spectrum (b0a6's T2/T3 objects).
This probe therefore:

- **reuses** the b0a6 exact-LE order-ideal DP verbatim (`Poset`, `before_prob_dp`,
  the LCG poset sampler), and
- **adds** an order-ideal DP transport matrix `transport_dp` — `T_P[x][a] =
  Pr[x at position a]` summed over the poset's order ideals, `O(#ideals · n)`,
  which for bounded-width families is polynomial and reaches `n = 16` in
  milliseconds. `λ_std` is an `n×n` eigensolve on `T_P|_H`, never an `S_n` object.

**Validation.** `transport_dp` was cross-checked against b0a6's brute-force
`transport_matrix` on **all 120** both-connected + named posets `n = 3..6`:
**0 mismatches** (`--validate`). Every reported quantity is exact rational LE
arithmetic cast to float only for the eigensolve.

---

## Method — the L4 kill test

For a poset `P` on `[n]` with a near-ordinal-sum cut `A | B` (`A` a prefix of the
expected-rank order `e`), define the interface leakage
```
ε = Δ₁(A) = E_σ|A ∖ σ(A)| / min(|A|,|B|),   E_σ|A∖σ(A)| = Σ_{x∈A} Pr[pos(x) ≥ |A|].
```
Let `S` be the **smaller** side. The minimal-counterexample induction hypothesis
says `P[S]` (a strictly smaller poset, hence not a counterexample) **has** a
balanced pair — an incomparable `{x,y} ⊆ S` with `p^{P[S]}_xy ∈ [⅓,⅔]`. Near-
ordinal-sum stability claims **that pair survives in the full poset**:
`p^{P}_xy ∈ [⅓,⅔]` when the interface is thin. We test exactly this and track:

- **`survives`** — does at least one balanced-in-side pair stay in `[⅓,⅔]` in `P`;
- **`D`** — the within-side perturbation `max |p^{P}_xy − p^{P[S]}_xy|` (the modulus);
- **RED trigger (ticket-defined)** — small `ε`, **neither** side a chain, and **no**
  within-side balanced pair in `P` on **either** side (the only balance, if any, is
  via cross pairs — i.e. the interface killed the within-side structure).

**Test families** (all deterministic; LCG-seeded, no clock/`Math.random`):

1. **Controlled near-ordinal-sums** — `P = A ⊕ B` with `m` interface relations
   **deleted**, tuning `ε` continuously from 0 upward. Blocks up to `8AC⊕8AC`
   (n=16); both symmetric (diagonal) and asymmetric (corner) deletions. *The direct
   handle on the thin-interface regime.* (361 posets, n 5–16.)
2. **Grown N-poset analogues** — stacked `N⊕N⊕…`, widened N's, fences/zigzags,
   `N⊕mAC⊕N`. *Does the b0a6 fat-interface pathology persist, and does it ever
   occur with small `Δ₁` at larger n?* (13 posets, n 6–16.)
3. **Sampled both-connected posets** `n = 8,9,10`, filtered to small best-prefix
   `Δ₁ ≤ 0.20` (thin interface). (6555 posets.)

---

## Results

### 1. The endgame form is universal — **0 RED events**

Across **all 6681** posets with both sides non-chain, **≥1 side keeps a
within-side balanced pair in `P`**: survival rate **1.0000**, RED events **0**.
This holds up to `n = 16` and, decisively, **in the high-`λ_std` band the
programme cares about**: among the **3180** posets with `λ_std ≥ 0.85` **and** a
thin interface `ε ≤ 0.10`, endgame survival is **100.0%**.

The single cleanest witness — a genuinely thin interface at large `n` in the
bad-mixing regime:

| `8AC ⊕ 8AC`, one cross-relation deleted | value |
|---|---|
| `n` | **16** |
| `ε = Δ₁` | **0.0019** (thin) |
| `λ_std` | **0.996** (near-1 / bad-mixing regime b0a6 could not reach) |
| smaller side `S` | 8-antichain, **28** balanced-in-side pairs |
| surviving in `P` | **28 / 28** |
| within-side perturbation `D` | **0.0077** |

A one-relation defect in an `n=16` ordinal sum barely moves the within-side
probabilities (`D < 0.01`) and every balanced pair survives — the thin-interface
limit behaves exactly as the stability conjecture predicts.

### 2. The empirical modulus `F(ε)`

Envelope (worst-case within-side drift over all posets with leakage `≤ ε`):

| `ε ≤` | `F(ε) = max D` | # posets | smaller-side survive rate |
|---|---|---|---|
| 0.02 | **0.073** | 265 | 1.0000 |
| 0.05 | **0.198** | 1172 | 1.0000 |
| 0.10 | **0.346** | 3403 | 0.9938 |
| 0.15 | 0.367 | 5635 | 0.9890 |
| 0.20 | 0.367 | 6601 | 0.9870 |

`F(ε) → 0` as `ε → 0` (a within-side probability cannot drift far when the
interface is thin), and the drift **saturates** near `0.37` — it never approaches
the full `⅓`-to-`⅔` window width from a centred pair. A power fit gives
`D ≈ 0.32·ε^{0.55}` (a linear `D ≈ ε` bound holds as an envelope for the small-`ε`
head but overstates the saturated tail). **Because the balanced-in-side interval
has width `⅓ ≈ 0.333` and `F(0.05) ≈ 0.20 < 0.333`, a pair sitting comfortably
inside the side's interval (e.g. `p^{side} = ½`) cannot be pushed out at
`ε < 0.05`** — the source of the clean small-`ε` survival.

### 3. The smaller-side-only reading — the honest AMBER refinement

The **stricter** reading (the note's Sec. 13 emphasis on reducing to the *smaller*
side) is **not** uniform: **89** posets lose *every* balanced pair on the smaller
side. But this is bounded and well-characterised, **not** a programme threat:

- **first loss at `ε = 0.085`** — the smaller side is unconditionally stable below
  that (no thin-limit failure);
- losses concentrate on **fragile** sides — `|S| ∈ {2,3,4}` with **few**
  balanced-in-side pairs (66/89 have exactly **one**); a side with one balanced
  pair has nothing to fall back on;
- they cluster at **high `λ_std ≈ 0.86–0.92`** (the interesting near-bad-mixing
  band), i.e. exactly where thinning bites hardest;
- **in every single one of the 89 cases the *bigger* side retains a within-side
  balanced pair** (bigger side never a chain, `survives = True` in all 89). The
  minimal-counterexample argument reduces to *either* proper side, so it always
  closes.

**Reading.** A correct L4 lemma must be free to **pick the side** (or use the
larger side when the smaller is fragile); the naïve "always reduce to the smaller
side" phrasing is false at moderate leakage. This is a precise, load-bearing
instruction for the proof, and the exact analogue of b0a6's finding that L2's
*literal* monotonicity lemma is false while the *thing it produces* survives.

### 4. Grown N-posets do **not** reproduce a thin-and-fatal pathology

The b0a6 `Δ₁ = 0.5` N-poset interface was the **best-Rayleigh** prefix. At the
**thinnest** (min-`Δ₁`) prefix — the actual near-ordinal-sum candidate — every
grown N analogue (stacked/widened/fence/`N⊕AC⊕N`, n up to 16) has a thin cut
available with `ε ≤ 0.162` and the balanced pair **survives** there. The fat
interface is a property of the *wrong* cut, not an obstruction at the ordinal-sum
cut. No grown-N poset was found with small `ε` and no surviving pair.

---

## Skeptical bar (carried from b0a6)

- **A high `λ_std` / Rayleigh quotient is still NOT near-ordinal-sum evidence.**
  This probe does not claim otherwise. It tests only the **stability step** —
  *given* a thin interface (which we impose by construction / by filtering), does a
  balanced pair survive — and answers **yes** in the endgame form.
- **`λ_std → 1` is still borrowed (L1).** The probe manufactures thin interfaces
  directly; it does **not** show a minimal counterexample *must* have one. That
  implication is L1 (bad BK mixing ⟹ `λ_std ≈ 1`), the proof/theory crux shared
  with the Čech/F-series program, and is **out of scope** here.
- **The exact rational LE arithmetic is not floated** except for the final
  eigensolve; survival/`D` are computed from exact `Fraction` before-probabilities.

---

## Where this leaves the programme

b0a6 returned "**ALIVE**, risk localized to **L1** (borrowed BK bad-mixing) and
**L4** (near-ordinal-sum stability vs the N-poset)." This probe **closes the
compute-testable part of L4 in the endgame form**:

1. **L4 (stability step): GREEN in the endgame form.** Given a thin interface, a
   balanced pair survives on ≥1 side across every tested poset up to n=16 and
   `λ_std` up to 0.996 — with an explicit modulus `F(ε)` and the precise caveat
   that the proof must be free to choose the side.
2. **L1 (bad BK mixing ⟹ `λ_std ≈ 1`) is now the *sole* surviving risk** and is a
   proof/theory question, not a compute target. Per b0a6 + PM review it is the
   **same open crux the Čech/F-series cohomology program is chasing**.

**Strategic consequence (for pm-onethird / Daniel).** With L4's stability step
de-risked, the programme's remaining gap is **exactly L1**. The highest-value next
question is the one b0a6 already flagged: **is "BK bad-mixing for minimal
counterexamples" itself the real target**, with *both* the spectral/near-ordinal-
sum program and the Čech/F-series program as downstream consumers? That is a
theory decision, not a probe.

---

## Reproduction

```
# venv with numpy (no repo dependency; pure-Python exact LE engines otherwise)
python scripts/onethird_mg3ce3_L4_near_ordinal_stability_probe.py --validate            # transport_dp vs b0a6 brute
python scripts/onethird_mg3ce3_L4_near_ordinal_stability_probe.py --families all --dump  # full sweep + data/ table
python scripts/onethird_mg3ce3_L4_near_ordinal_stability_probe.py --families nos         # near-ordinal-sum family only
```

All randomness is a seeded LCG; results are bit-reproducible (verified: two
independent full runs produce identical summaries).

## Data appendix — headline aggregates

| metric | value |
|---|---|
| posets analyzed / stability points | 6929 / 6681 |
| max `n` reached | **16** |
| max `λ_std` | **1.0000** (exact ordinal sums), 0.996 at n=16 thin |
| **endgame-form survival (≥1 side)** | **1.0000** over 6681 (RED events: **0**) |
| high-`λ` thin band (`λ≥0.85`, `ε≤0.10`) endgame survival | **100.0%** (3180 posets) |
| exact ordinal sums (`ε=0`) all survive | 64 / 64 |
| smaller-side-only losses | 89 (all covered by bigger side; first at `ε=0.085`) |
| envelope `F(0.02)/F(0.05)/F(0.10)` | 0.073 / 0.198 / 0.346 |
| smaller-side survive rate `ε<0.05` | **1.0000** |
| `transport_dp` vs brute cross-check | 0 mismatches / 120 posets |
