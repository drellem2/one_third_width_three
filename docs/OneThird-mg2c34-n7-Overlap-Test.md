# OneThird — the n=7 overlap test (mg-2c34)

**Status: RED for the prediction under test. The corpus predicted `c ≈ 0` at the three named
n=7 off-regime posets; the measured value is `c ≈ 0.9966`.**

> **AUDITED (mg-09ea, verdict OVERSTATED) — consequences landed in place 2026-07-29 by mg-60d3.**
> The arithmetic is **CONFIRMED exhaustively**: every measured figure was reproduced from
> definitions by a disjoint route, and the population claim confirmed twice — once with **no
> enumeration at all**. **Not one number is wrong.** What was struck is one inference (§6(a)'s
> *"no explanatory power"*, refuted by this document's own dataset) and two instrument gaps that
> let mutations pass CI. **§14 is the ledger of what changed and what did not** — read it before
> quoting any summary line from this file. Where this document and the audit disagree, **the audit
> wins**; audit: `docs/OneThird-mg2c34-n7-Overlap-Test-IndependentAudit.md`.

Ticket: mg-2c34, repo `one_third_width_three`. Computation permitted (Daniel, 2026-07-29: the
no-computation directive *"was a specific directive for the time when I said it, it's not a blanket
prohibition"*). First ticket filed under that clarification.

Artifacts, all committed:

| what | path |
|---|---|
| the instrument + all controls + the sweep | `scripts/onethird_mg2c34_n7_overlap_test.py` |
| every number below | `data/onethird-mg2c34-n7-overlap.json` |
| prior data re-verified, not re-derived | `data/onethird-mg8b64-L1b-bk-transport-transfer.json` |
| the independent audit's own sweep (§6, §6.1 project from it) | `data/onethird-mg09ea-independent-audit.json` |
| the repaired gate's mutation demonstration (§2.6.1) | `scripts/onethird_mg60d3_gate_mutation_demo.py`, `data/onethird-mg60d3-gate-mutation-demo.json` |

Reproduce in full with `/usr/bin/python3 scripts/onethird_mg2c34_n7_overlap_test.py` (numpy; the
interpreter matters — see §12). The script exits non-zero if any control fails, and runs in CI in
its fast mode (§2.6). Nothing in this document is asserted from a number that is not in a committed
JSON.

---

## §0 — Headline

1. **The prediction is refuted.** `c(enum-n7-#3) = 0.995552`, `c(#20) = 0.996857`,
   `c(#600) = 0.996549`. The corpus predicted `c ≈ 0`. The `λ₂^BK` eigenspace is **simple** at all
   three, so `c_max = c_min` — there is no "most favourable reading" loophole; this is also the
   adversarial reading. The random-subspace null is `0.067 / 0.111 / 0.152`, so `c ≈ 0.9966` is
   6.6–15× the null: not a dimension artifact.

2. **It is not three posets — it is every n=7 both-connected poset there is.** Measured on all
   **956** `n = 7` **both-connected** isomorphism classes (mg-8b64's dedup had dropped 10; §5.1
   finds and measures them):
   `c ∈ [0.978492, 0.998529]`, median `0.994751`. Not one poset has small overlap.
   `corr(c, δ) = 0.055` — `c` is essentially **independent of `δ`**, i.e. of the frozen-regime
   coordinate the "conditional" picture is stated in.

3. **The stated mechanism is refuted, and by a hand argument, not only by the sweep.** The corpus
   inferred `c ≈ 0` from *"the slow mode is explicitly degree-2 — a lone frozen pair"*. That
   inference is invalid: the frozen pair indicator `1[x <_σ y]` is a degree-2 function of `σ` that
   **can lie entirely inside the one-particle span `U` once restricted to `L(P)`**. Lemma 3.1 below
   proves this in three lines; the sweep finds it happening **exactly** (`‖P_U f‖²/‖f‖² = 1` to
   `1e-9`) in **137 of the 946** posets — Lemma 3.1's hypothesis holds at **all 137** — and never
   below `0.779`. A named non-vacuous witness: `enum-n7-#86`, where `U` occupies `15.6%` of the
   space and the degree-2 pair indicator sits exactly inside it.

4. **The consequential finding is not the refutation — it is what replaces it.** `c` is pinned
   inside a 2%-wide band across the entire population, while the modulus the L1b transfer would
   actually need, `R = (1−λ_std)/(1−λ₂^BK)`, ranges over `[0.99, 19.93]`. And
   **`corr(c, R) = +0.50` — the wrong sign** for a control inequality *"high overlap ⟹ small
   required modulus"*. The sign result is monotone across the whole population, not an outlier
   artifact: median `R` climbs from `2.90` in the bottom `c`-decile to `7.99` in the top, and
   `R > 15` **forces** `c ≥ 0.994228` (§6, decile table). So `c` is **not a valid control
   parameter** — which is a different and weaker statement than "`c` says nothing about `R`", and
   only the first is true.

   > **[CLAUSE STRUCK 2026-07-29 by mg-60d3, on mg-09ea §4.1 (F1).]** This point previously read
   > *"So **`c` has no explanatory power for the transfer at n=7**: knowing `c` across its whole
   > observed range constrains `R` to its whole observed range."* That clause is **BROKEN, and
   > refuted by this document's own dataset.** Its derivation read *`c` spans 2%, `R` spans 20×* as
   > *`c` cannot explain `R`*; **range width is not explanatory power** (a variable confined to a
   > narrow range can determine a wide-range one exactly — `R = 924(c − 0.9785) + 0.99` has
   > correlation `1`). Measured: `c` accounts for **25% of `R`'s variance**, and conditioning on the
   > bottom `c`-decile confines `R` to `[1.07, 5.77]` — a quarter of the span. The replacement above
   > is §6(b), and §6(b) is **stronger** than what was struck. **Ledger claim 12 is unchanged and
   > survives as worded** (§11); what failed is its stated derivation and this prose.

5. **What was never checkable at all.** The conditioning hypothesis of the "conditional
   standard-dominance" picture — *all-pairs-frozen*, i.e. `δ(P) < 1/3` — is **satisfied by no
   poset anywhere in the mg-8b64 ensemble** (1091 rows; `min δ = 1/3` exactly, `0` rows below).
   For any poset **with at least one incomparable pair**, `δ(P) < 1/3` says *every* incomparable
   pair is unbalanced — which **is** what it means for `P` to be a counterexample to the 1/3–2/3
   conjecture. So the regime contains **no non-chain poset** at any `n` unless the **general**
   conjecture is false; a width-3 witness would additionally refute the width-3 case, which is the
   statement this programme exists to prove, but a width-≥4 witness would not. *(Both qualifiers
   restored here 2026-07-29 — mg-60d3, on mg-09ea F6; §7 has the full statement.)* **Both**
   the corpus's "off-regime" rows
   (`δ = 0.500`) and its "in-regime" rows (`δ = 0.381`, `0.360`) sit outside the conditioning
   hypothesis. The picture was inferred entirely from a `δ = 0.5` vs `δ ≈ 0.37` contrast and then
   labelled with a regime boundary at `1/3` that neither side is on.

**Net.** A prediction the corpus called *"the single highest-value follow-on"* and *"the decisive
next experiment"* is refuted, its mechanism is refuted by hand, and the quantity it was about is
shown to be the wrong control parameter. The 1/3-programme's architecture is not damaged: nothing
here touches Steps 1–8. What is damaged is the belief that the overlap form of standard dominance
is the missing ingredient in L1b. It is not missing — it already holds, uniformly, and it is not
enough.

---

## §1 — The target, pinned from the corpus (quoted, not reconstructed)

The ticket requires the target be pinned by quotation and the work stopped if the corpus disagrees
with itself. **It does not disagree.** All three components resolve to a single definition.

### 1.1 Which quantity `c` is

`scripts/onethird_mg4a86_sdquant_overlap.py`, module docstring:

> `SD-quant(c)`: the slowest BK mode `f` satisfies `‖P_U f‖² ≥ c ‖f‖²`, where
> `U = span{ σ ↦ 1[σ(a)=x] }` is the one-particle observable span. This is well-posed **without**
> `U` being invariant (which it is not on `L(P)`).

and, operationally, from the same file:

> take the BK eigenspace at `lambda_2` (excluding the constant mode), compute the LARGEST overlap
> over that eigenspace (the most favourable reading, which matters because `lambda_2` is frequently
> degenerate): `c(P) = lambda_max( Vᵀ P_U V )`, `V` = orthonormal basis of the eigenspace.

### 1.2 Which three posets

`docs/OneThird-StandardDominance-ComparisonRoute.md` §7.3:

> **The decisive next experiment**, cheap and well-specified: compute `c(P)` on
> `enum-n7-#600/#3/#20` from the `mg-8b64` data. Predicted outcome `c ≈ 0`, which would show
> SD-quant is *conditional* on the all-pairs-frozen regime […] **Flagged as the single
> highest-value follow-on.**

Those names are indices into `enumerate_both_connected(7)` from
`scripts/onethird_mgb0a6_spectral_killshot_probe.py` — mg-8b64's own naming
(`targets.append((f"enum-n{n}-#{i}", P))`). They are the off-regime block of
`docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:295-297`.

### 1.3 Under which measure

The BK walk is the repo's lazy `(n−1)`-regular convention (`step8.tex`): each of the `n−1` adjacent
position slots contributes `1/(2(n−1))` to a swap if the pair there is incomparable and to the
self-loop otherwise. That matrix is **symmetric and doubly stochastic**, so its stationary measure
is **uniform on `L(P)`** and the `L²(π)` inner product is Euclidean up to the global `1/|L(P)|`.
`P_U` is therefore the ordinary orthogonal projector and `c` is measure-unambiguous.

**Consistency check, not assumption.** Two files in the corpus build this matrix independently —
`onethird_mg8b64_..._probe.py:bk_walk_matrix` and
`onethird_mg4a86_standard_dominance_target_audit.py:bk_walk_matrix`. They agree, and CHECK-0
(§2.5) verifies the whole instrument agrees with mg-4a86's to `0.0e+00`.

### 1.4 One thing the corpus does *not* say, which matters

`U` is *not* the standard irrep in general — it is the restriction to `L(P)` of the one-particle
span. On `L(P) = S_n` (the antichain) the two coincide: `span{σ ↦ 1[σ(a)=x]}` is the matrix-coefficient
span of the permutation representation `triv ⊕ std`, so `U ⊖ constants` is exactly the standard
isotypic component. On a proper `L(P) ⊊ S_n` the identification is only by analogy. **The corpus
uses "standard sector" and "one-particle span" interchangeably; this document uses the definition
that is actually computed (`U`), and §3 shows the difference is exactly where the mechanism claim
breaks.**

---

## §2 — The instrument, and the controls run before trusting it

The ticket requires a positive control demonstrating the instrument **can produce the wrong
answer** on a case with a known answer. Four controls; all are in the script and all outputs are in
the JSON.

### 2.1 CONTROL A — graded analytic control (the one that matters)

On a real `L(P)` (`enum-n7-#600`, `|L| = 132`), build a synthetic symmetric walk whose `λ₂`
eigenvector is `v(θ) = cos θ · u + sin θ · w`, with `u` a unit vector inside `U ∩ 1^⊥` and `w` a
unit vector orthogonal to `U`. Spectrum by construction: `1` (constants), `0.9` (`v`), `0.3` (rest).
The true answer is `c = cos²θ`, known in closed form at every `θ`.

| `θ` | expected `c` | measured | abs err |
|---|---|---|---|
| 0° | 1.000000 | 1.000000000 | 0.0e+00 |
| 30° | 0.750000 | 0.750000000 | 3.3e-16 |
| 45° | 0.500000 | 0.500000000 | 2.2e-16 |
| 60° | 0.250000 | 0.250000000 | 1.1e-16 |
| **90°** | **0.000000** | **0.000000000** | **8.8e-18** |

The 90° row is the point of the control: **the instrument returns `0` when `0` is the right
answer.** An instrument that cannot output `0` cannot refute SD-quant, and the §4 measurement would
be a check that could not fail. This one can fail, at every point of a continuum, and does not.

### 2.2 CONTROL B — known-answer poset

Antichain `A_n`, `n = 4,5,6`: `L(P) = S_n`, the BK chain is the interchange process on the path, and
by Aldous/Caputo–Liggett–Richthammer the slowest mode **is** the single-particle mode, which lies in
`U`. Required and measured: `c = 1.000000000` at all three.

### 2.3 CONTROL C — deliberately broken instrument, which must fail CONTROL B

Same computation, with `U` replaced by a fixed coordinate subspace of the *same dimension*. True
answer still `1`; broken instrument returns `0.5546 / 0.2905 / 0.1247`. This is what makes CONTROL
B non-vacuous: `c = 1` on the antichain is a fact about `U`, not a fact about `dim U`.

### 2.4 CONTROL D — dimension-artifact null

`U` replaced by a **random** subspace of the same dimension (seeded, 20 draws). Measured means
`0.065490 / 0.112038 / 0.159185` against the analytic null `dim U / |L| = 0.066667 / 0.111111 /
0.151515` at `#3 / #20 / #600`; the largest of the 60 draws is `0.2288`. Any `c ≈ 1` surviving this
substitution would have been an artifact of `dim U`. None does — the measured `c ≈ 0.9966` sits
6.3–15× above the null, and above every individual draw by a factor of 4.

*(The seed is `default_rng(20260729 + <deterministic name key>)`. It deliberately does **not** use
Python's `hash()`, which is salted per process — that would have made this control's numbers differ
between runs, in a document whose whole claim is that every number is reproducible. Verified
identical across two runs.)*

### 2.5 CHECK-0 — instrument equivalence

This document's `c_max` and mg-4a86's `sd_quant_constant` agree to **`0.0e+00`** on every poset
measured. The measurement is mg-4a86's own instrument, extended (§2.7), not a re-implementation
that could differ from it.

### 2.6 The controls are wired to a non-zero exit code, and mutation-tested

A control nobody can fail is indistinguishable from no control at all — the mg-4ad1 lesson, applied
to this file. The script **exits non-zero** if CONTROL A, B or C fails, if CHECK-0 disagrees by more
than `1e-12`, if any of the **five** named posets stops matching its committed mg-8b64 row **on any
of `|L|`, `λ_std`, `δ` or `λ₂^BK`**, or if a degenerate `λ₂` ever makes the reported `c`
reading-dependent. It is wired into `.github/workflows/script-controls.yml` in `--no-sweep` mode,
alongside the existing mg-8489 and mg-8ff1 controls.

> *"three" → "**five**" corrected 2026-07-30 (mg-5ad1, §7). The identity loop runs over `named` =
> `OFF_REGIME + IN_REGIME`, and §2.6.1's own table already listed all five (`#3/#20/#600/#809/#945`);
> mg-5ad1's M1 run fails 5 of 5. The error understated the gate's coverage.*

**Mutation-tested, because "exits non-zero on failure" is itself a claim:**

| mutation | caught by | exit |
|---|---|---|
| `projector_U` → a random subspace of the same dimension | CHECK-0 (`9.06e-01` disagreement) | **1** |
| `U` genuinely shrunk (even **positions** only) — invisible to CHECK-0, since both instruments then share the wrong `U` | CONTROL B (`c = 0.573 / 0.724 / 0.530` on the antichains) | **1** |
| drop element `0`'s position observables from `U` | *nothing — and correctly so* | 0 |
| **M1** — BK step `1/(n−1)` instead of `1/(2(n−1))` | ~~nothing~~ → **the identity check's `match_bk_lambda2`** *(repaired)* | **1** |
| **M2** — `U` shrunk by **element** block (elements `0` **and** `1` dropped) | ~~nothing~~ → **CONTROL B's `c_min`** *(repaired)* | **1** |

The third row is not a gap. Dropping any single element's block is a **no-op on `U`**: since
`Σ_x 1[σ(a)=x] ≡ 1`, that block already lies in the span of the others together with the constant,
and `dim U` is unchanged (`10 / 17 / 26` before and after). The gate is right not to fire. **But the
general claim that row implies — that CONTROL B covers `U` shrinks — is false**, and M2 is the
witness: CONTROL B caught the *position*-block shrink and did not catch the *element*-block one.

#### 2.6.1 The two repairs, and the demonstration that they fire (mg-60d3, on mg-09ea F3/F4)

> **[Landed 2026-07-29.]** mg-09ea ran its own mutations against the shared dependency modules — so
> that *both* this measurement and mg-4a86's reference instrument see the bug, which is the
> realistic case for a coding error — and found **two that passed this gate**. mg-2c34 had wired
> `script-controls.yml` to run these controls, so a gate that could not fail was **load-bearing in
> CI**. Both repairs use values the script **already computed and threw away**; one line each.

**F3 — `λ₂^BK` had no control that could fail, and the check that would cover it was *fetched and
discarded*.** Under M1 the three headline `λ₂^BK` values become `0.961846 / 0.962405 / 0.959841`
instead of `0.980923 / 0.981202 / 0.979921`, every `R` in §6 roughly halves, §4's column is wrong
and §9's *"the `λ₂^BK` and `λ_std` columns reproduce the corpus's numbers exactly"* is falsified.
Nothing caught it, and each miss had a reason: **CONTROL A never calls `bk_walk_matrix`** (it
synthesises its own `W` from a chosen spectrum); **CONTROL B/C are eigenvector-only**, and a global
rate rescaling fixes every eigenvector — the demonstration confirms this exactly, `c` under M1 is
**bit-identical** at all five posets (`0.995552 / 0.996857 / 0.996549 / 0.987947 / 0.995256`) while
every `λ₂^BK` moves; **CHECK-0 shares the code** (§11.1); and the identity check
set `rec["ref_bk_lambda2"]` and then built only `match_num_LE`, `match_lambda_std`, `match_delta`.
The one committed reference value for the only genuinely **dynamical** quantity in the document —
the denominator of `R`, which is the whole substance of §6 — was loaded into the report and never
compared. **Repair:** `λ₂^BK` is now recomputed in the identity block and `match_bk_lambda2` is in
the gate's conjunction (`_identity_row_ok`). *The number was never wrong* — mg-09ea's independent
Laplacian route agrees with the committed reference to `≤ 2.5e-15` — so this was **missing control,
not wrong result**. But under Appendix A's own standard, a passing result whose check could not fail
is unsupported.

**F4 — CONTROL B gated on `c_max` only, and computed `c_min` without asserting it.** Under M2 the
headline values move to `0.986571 / 0.988475 / 0.995959` (`#3 / #20 / #600`; `dim U` drops
`10/17/26 → 7/13/21` on the antichains, so `U` is genuinely smaller) and the gate exited 0: on the
antichain the
shrunk `U` still meets the `λ₂` eigenspace, and `c_max` is a **maximum over that eigenspace**, so
the favourable reading survives a shrink the adversarial reading does not. **This is the same
one-sidedness §2.7 identifies as the reason to report `c_min` at all** — it was added to the
measurement and not to the control. The already-computed value separates the cases perfectly:

| antichain | true `U`: `c_max` / `c_min` | shrunk `U`: `c_max` / `c_min` |
|---|---|---|
| `A₄` | 1.000000000 / **1.000000** | 1.000000000 / **0.000000** |
| `A₅` | 1.000000000 / **1.000000** | 1.000000000 / **0.000000** |
| `A₆` | 1.000000000 / **1.000000** | 1.000000000 / **0.000000** |

**Repair:** `B_PASS_c_is_1` now requires `|c_min − 1| < 1e-8` as well as `|c_max − 1| < 1e-8`
(`_antichain_row_ok`).

**Both repairs are demonstrated to FIRE**, because a control asserted and not shown to fire is the
exact defect this arc keeps producing. `scripts/onethird_mg60d3_gate_mutation_demo.py` runs the
full CI gate six times and asserts the whole exit-code matrix
(`data/onethird-mg60d3-gate-mutation-demo.json`):

| | pre-repair gate | repaired gate |
|---|---|---|
| unmutated instrument | exit **0** | exit **0** — neither repair fires on a healthy instrument |
| **M1** (BK step) | exit **0** ← the defect | exit **1** — `enum-n7-#3/#20/#600/#809/#945` all fail `match_bk_lambda2` |
| **M2** (`U` shrunk) | exit **0** ← the defect | exit **1** — CONTROL B fails on `A₄`, `A₅`, `A₆` |

The pre-repair gate is reconstructed **inside the demo**, by substituting the two predicates' old
bodies; the deliverable's gate has no switch that weakens it and must not acquire one. The demo is
**itself a control** — it exits non-zero if that matrix is not observed exactly. It is **not** in CI:
six full gate runs is ~12 min, far outside the order-seconds rule `script-controls.yml` states at the
top. Run it on demand when the gate changes.

> **[mg-5ad1, independent audit of this repair, 2026-07-30 — see
> `docs/OneThird-mg60d3-GateRepair-IndependentAudit.md`.]** The 2×3 matrix above **REPRODUCES** by a
> disjoint route (the actual pre-repair source at `87f0424` plus source-level mutations of the
> defining modules, rather than the demo's in-process predicate substitution); every figure in §2.6
> and §2.6.1 is confirmed exactly, and ledger claim 27 stands. Two findings on the **residual**, which
> this section does not claim to have closed:
>
> 1. **The repairs close two instances of a class, not the class.** Two further one-line mutations of
>    the same family pass the repaired gate with *"All controls and identity checks PASSED"*: flipping
>    mg-8b64's Theorem-E frozen-pair selector `min` → `max` (which moves `frozen_pair` at 5/5 posets
>    and `frozen_pair_overlap_with_U` from `0.807/0.809/0.810` to exactly `1.0000` — the quantity
>    **ledger claim 8** rests on), and dropping `projector_U`'s rank filter (which inflates `dim U` to
>    `|L|` at `#945`/`#809`, so `c = null = 1.0000` and the measurement is vacuous by this document's
>    own §2 criterion). The first is **F3 verbatim**: `frozen_pair` is a field of the *same* committed
>    mg-8b64 row the gate already opens, and the identity conjunction compares **4 of its 22 fields**.
> 2. **"Run it on demand when the gate changes" is insufficient even when obeyed.** The demo's
>    `EXPECTED` is a hardcoded 2×3 matrix over two fixed mutations, so it is a regression test on the
>    two known repairs and would not have caught either mutation above.
>
> Audited in both directions as well: the F4 `c_min` assertion is **non-vacuous**
> (`dim λ₂-eigenspace = n−1 = 3/4/5`), **not over-tight** (`1 − c_min ≤ 2.7e-15` against a `1e-8`
> tolerance), and **not knife-edge** (`3.0e7–1.1e8 ×` `EIG_TOL` of margin). Its stated justification
> does over-reach: Aldous/CLR gives the gap *eigenvalue*, while `c_min = 1` asserts gap-*eigenspace*
> containment in the one-particle sector — verified here at `n = 4,5,6` **and `7`**, but not licensed
> by that theorem for a larger antichain.

### 2.7 What this instrument adds over mg-4a86's

mg-4a86 reports only `c_max = λ_max(Vᵀ P_U V)` — the *most favourable* reading over a possibly
degenerate `λ₂` eigenspace. For a **refutation** that is the wrong tail: one standard mode hiding
inside a degenerate eigenspace would give `c_max ≈ 1` while the actual slow dynamics is
non-standard. This script also reports `c_min = λ_min(Vᵀ P_U V)` (the adversarial reading), the
eigenspace dimension at both `1e-9` and a wider `1e-6` band, and the null `dim U/|L|`.

**Result: the concern is empty here.** `λ₂` is **simple** at all three named posets and in
**99.58%** of the 946-poset population (max eigenspace dimension 2, at either tolerance), so
`c_min = c_max` throughout. The favourable and adversarial readings coincide.

It also takes mg-8b64's **own** Theorem-E frozen pair for the mechanism test of §3 (the `argmin` of
`E(f_xy)/Var(f_xy)`), not the max-bias pair — at these posets they are **different pairs**
(`#600`: frozen `(2,4)` at `p = 0.5`; max-bias at `p = 0.894`), and the corpus's claim is about the
frozen one.

---

## §3 — The mechanism claim, tested and refuted by hand

The corpus's prediction was not a guess; it was an inference:

> A genuinely degree-2 slow mode has **small** overlap with `U`, i.e. `c ≈ 0` there.
> — `OneThird-StandardDominance-ComparisonRoute.md` §7.3

resting on `OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:302-306`:

> A genuinely slow BK mode exists (`λ₂^BK ≈ 0.98`), but it is **non-standard** (degree-2, the lone
> frozen pair) […] the low-energy cut lands in the wrong irrep.

**The inference is invalid**, and the reason is §1.4: on `S_n`, "degree-2" and "outside the
one-particle span" coincide; on `L(P) ⊊ S_n` they do not, because the order constraints can make a
degree-2 function of `σ` agree with a degree-1 function *on `L(P)`*, which is the only place it is
evaluated.

### Lemma 3.1 (elementary; no computation) — a degree-2 pair indicator can lie exactly in `U`

*Let `x ∥ y` in `P`. Suppose there is a position `k` such that for every `σ ∈ L(P)`,*
`x <_σ y ⟺ pos_σ(x) ≤ k`. *Then*

  `1[x <_σ y] = Σ_{a ≤ k} 1[σ(a) = x] ∈ U`  *exactly.*

*Proof.* Both sides are functions on `L(P)`; the right side is `1[pos_σ(x) ≤ k]`, which by
hypothesis equals the left side pointwise. The right side is a sum of one-particle observables,
hence in `U`. ∎

**Hand-checkable witness family.** `P = 1 ‖ chain_m`: a single free element `z` incomparable to a
chain `c_1 < ⋯ < c_m` (`n = m+1`; the corpus's own `1||chain5/6/7` in `named_posets()`). `L(P)` has
`m+1` elements indexed by `pos_σ(z)`. For the pair `(z, c_j)`: `z <_σ c_j ⟺ pos_σ(z) ≤ j`. Lemma
3.1 applies with `k = j`, so the pair indicator — a degree-2 function of `σ` — is **exactly** a
one-particle observable on `L(P)`.

> **Vacuity caveat, stated because the data forces it.** On `1 ‖ chain_m`, `dim U = |L(P)| = m+1`:
> `U` is the *whole* space, so "the pair indicator is in `U`" is true but trivial there, and the
> measured `c = 1.000000` at those rows carries **no** information (their null is `1.0`). This
> family is a clean illustration of the lemma and **not** evidence. The evidence is the next
> paragraph.

**Non-vacuous witness, from the sweep.** `enum-n7-#86`: `|L| = 90`, `dim U = 14`, null `= 0.156`.
Its Theorem-E frozen pair is `(2, 6)` with `p = 0.80`, and — verified in the script — for **every**
`σ ∈ L(P)`, `2 <_σ 6 ⟺ pos_σ(2) ≤ 2`. Lemma 3.1 applies with `k = 2`, so the degree-2 pair
indicator lies **exactly** in a subspace occupying `15.6%` of `L²(L(P))`. Here the conclusion is not
trivial, and it is the opposite of `c ≈ 0`.

### 3.2 The same thing, measured, across the population

For each poset the script takes mg-8b64's **own** Theorem-E frozen pair (`argmin` of
`E(f_xy)/Var(f_xy)` — not the max-bias pair, which is a different pair at these posets) and
measures the frozen-pair indicator's own overlap with `U`:

| | `#3` | `#20` | `#600` | `#945` | `#809` |
|---|---|---|---|---|---|
| `‖P_U f‖²/‖f‖²` for the frozen pair indicator | 0.8072 | 0.8094 | 0.8096 | **1.0000** | **1.0000** |

Over the 946-poset population: min `0.7794`, median `0.8728`, and **exactly `1` (to `1e-9`) in 137
posets**. The degree-2 pair indicator is never outside `U` by much and is often inside it exactly.

**Lemma 3.1 accounts for all of them.** The script checks the lemma's threshold hypothesis directly
at each of those 137 posets: it holds at **137 of 137**. So the exact-membership cases are not
numerical coincidences — they are instances of a three-line lemma, and the lemma is the reason the
corpus's inference fails.

**Consequence.** *"The slow mode is degree-2"* is true and *"the slow mode is outside `U`"* is
false, at the same posets, simultaneously. The step from the first to the second is the error.

---

## §4 — The measurement

`enum-n7-#600 / #3 / #20`, the three posets the corpus names. Identity is **re-verified, not
assumed**: `|L(P)|`, `λ_std` and `δ` are recomputed here and compared against the committed
mg-8b64 rows — all match (`|L|` exactly; `λ_std` and `δ` to `< 1e-9`).

| poset | `\|L\|` | `dim U` | `δ` | `λ₂^BK` | `λ_std` | `dim E` | **`c_max`** | **`c_min`** | null | corpus predicted |
|---|---|---|---|---|---|---|---|---|---|---|
| `enum-n7-#3` | 360 | 24 | 0.5000 | 0.980923 | 0.785048 | 1 | **0.995552** | 0.995552 | 0.0667 | `≈ 0` |
| `enum-n7-#20` | 198 | 22 | 0.5000 | 0.981202 | 0.767529 | 1 | **0.996857** | 0.996857 | 0.1111 | `≈ 0` |
| `enum-n7-#600` | 132 | 20 | 0.5000 | 0.979921 | 0.773911 | 1 | **0.996549** | 0.996549 | 0.1515 | `≈ 0` |
| `enum-n7-#945` (contrast) | 21 | 7 | 0.3810 | 0.943488 | 0.943926 | 1 | 0.987947 | 0.987947 | 0.3333 | — |
| `enum-n7-#809` (contrast) | 25 | 9 | 0.3600 | 0.969495 | 0.902015 | 1 | 0.995256 | 0.995256 | 0.3600 | — |

The `λ₂^BK` and `λ_std` columns reproduce the corpus's numbers exactly — `λ₂^BK ≈ 0.98` against
`λ_std ≈ 0.77` at the three, `λ₂^BK ≈ λ_std` at `#945`. **The corpus's arithmetic is right. Its
reading of that arithmetic is what fails.** The slow mode at `#600` is `99.65%` inside `U` while
`λ_std` is `0.21` below `λ₂^BK`.

**That gap is the load-bearing observation.** It is a quantitative demonstration of the
static-vs-dynamical category mismatch mg-4a86's audit named qualitatively: `λ_std` is a functional
of the stationary measure alone, *not* the BK generator restricted to `U`. Full overlap of the slow
mode with `U` does **not** make the two numbers close.

---

## §5 — The population: every n=7 both-connected poset

Three posets is a population of three. The whole `n = 7` both-connected population costs about two
minutes, so it was measured rather than extrapolated over. mg-8b64's deduped list (946 posets) is
the sweep block; §5.1 then finds and measures the 10 isomorphism classes that list drops, bringing
coverage to all **956** classes.

```
sweep block: 946    c_max: min = 0.978492   median = 0.994751   max = 0.998529
                    c_min: min = 0.978492   median = 0.994751     (λ₂ simple in 99.58%)
all 956 classes:    min c = 0.978492
```

Stratified by `δ`:

| `δ` band | count | `c` median | `c` min | `c` max | null median | frac `c > 0.9` | frac `c < null` |
|---|---|---|---|---|---|---|---|
| `[1/3, 0.40)` | 8 | 0.9921 | 0.9879 | 0.9978 | 0.3478 | 1.000 | 0.000 |
| `[0.40, 0.45)` | 117 | 0.9935 | 0.9823 | 0.9984 | 0.2619 | 1.000 | 0.000 |
| `[0.45, 0.50]` | 821 | 0.9948 | 0.9785 | 0.9985 | 0.1970 | 1.000 | 0.000 |
| `δ < 1/3` (the conditioning regime) | **0** | — | — | — | — | — | — |

`corr(c, δ) = 0.055`. The ten lowest `c` in the population are `0.9785 … 0.9800`, and they are **not**
the three named posets — those sit at or above the population median. There is no low-`c` tail at
`n = 7` to find.

### 5.1 The sweep is complete over isomorphism classes — a gap that was closed, not caveated

`enumerate_both_connected` dedups by `iso_signature`, and that function's own docstring says it is
*"not a perfect canonical form (used only to shrink reporting, never to gate a RED/GREEN)"*. It is
gating a claim here, so it was checked rather than trusted. The script canonicalises properly (min
over profile-preserving relabelings, cross-verified against a brute min over all `7!` permutations —
both give 956):

```
naturally-labelled both-connected n=7 : 52810
TRUE isomorphism classes              :   956
classes in mg-8b64's deduped list     :   946
classes DROPPED by its dedup          :    10   <- measured here
```

The 10 dropped classes give `c ∈ [0.992696, 0.998412]` (`|L|` from 60 to 181, nulls `0.12`–`0.25`).
Folding them in: **`c` is measured on all 956 `n = 7` both-connected isomorphism classes, and
`min c = 0.978492`.** The sweep is exhaustive over that class, not a sample of it.

*(Side effect worth recording for the corpus: mg-8b64's own reported "946 both-connected `n=7`
posets" undercounts by 10. Nothing in mg-8b64's conclusions turns on the 10 — they are ordinary
posets, `δ ∈ [0.45, 0.50]` — but the count is wrong wherever it is quoted.)*

### 5.2 Larger `n`, as a falsification probe only

The corpus's own family/named stress posets were measured so a larger-`n` case could break the
pattern. **Ten of the 29 rows are vacuous** (`dim U = |L(P)|`, null `= 1.0`) and carry no
information; they are excluded. Over the 10 rows with null `≤ 0.5`, `min c = 0.978898`
(`crown S3^0`, `n=6`). The informative large-`n` rows:

| poset | `n` | `\|L\|` | null | `c` |
|---|---|---|---|---|
| `fence7` | 7 | 272 | 0.0919 | 0.996946 |
| `fence8` | 8 | 1385 | **0.0260** | 0.997682 |
| `LEM-cyclic-witness` | 10 | 1008 | **0.0347** | 0.998516 |

At `n = 10`, `U` occupies `3.5%` of the space and the slow mode is `99.85%` inside it. **This is a
locked family** chosen by the corpus for unrelated reasons — it can falsify the pattern and cannot
establish it. It does not falsify it.

---

## §6 — What replaces the refuted picture: `c` is the wrong control parameter

L1b needs the transfer `1 − λ_std ≤ K · (1 − λ₂^BK)`. Define the modulus the transfer actually
requires at a given poset:

  `R(P) := (1 − λ_std) / (1 − λ₂^BK)`.

Over the 946-poset population:

| | min | median | max |
|---|---|---|---|
| `c` | 0.978492 | 0.994751 | 0.998529 |
| `R` | 0.9923 | 5.9703 | **19.9303** (at `enum-n7-#94`, `c = 0.998001`) |

`c` is confined to a band **2% wide**; `R` spans a factor of **20**. Two consequences were drawn
from that, both tightly scoped to `n = 7`. **The first does not follow and is struck; the second is
the finding, and it is stronger than it was stated.**

**(a) — STRUCK.**

> **[STRUCK 2026-07-29 by mg-60d3, on mg-09ea §4.1 (F1).]** §6(a) previously read: *"**`c` cannot
> explain `R`.** Conditioning on `c` anywhere in its observed range leaves `R` in essentially its
> whole observed range. Whatever distinguishes `R ≈ 1` posets from `R ≈ 20` posets, it is not the
> overlap."* It is **BROKEN, and refuted by the dataset this very section is computed from.** The
> inference was *`c` spans 2%, `R` spans 20× ⟹ `c` cannot explain `R`*, and **range width is not
> explanatory power**: the affine map `R = 924(c − 0.9785) + 0.99` takes `c`'s observed band onto
> `[0.99, 19.47]` with correlation `1`. No conditional-range table was ever computed, here or in the
> JSON. It is computed below, and it says the opposite. **What replaces §6(a) is the table, and the
> table is (b) restated more strongly.**

**(a′) `c` carries real information about `R` — and it is exactly the wrong information.**
Conditioning on `c` by decile, over all 956 classes (mg-09ea's independent sweep, §4.1 of the audit;
`data/onethird-mg09ea-independent-audit.json`):

| `c` decile | n | `c` range | `R` min | `R` max | `R` median | share of full `R` span |
|---|---|---|---|---|---|---|
| 1 (lowest `c`) | 96 | 0.978492 – 0.987176 | 1.073 | **5.770** | 2.896 | **0.248** |
| 2 | 95 | 0.987176 – 0.991508 | 0.992 | 8.704 | 3.810 | 0.407 |
| 3 | 96 | 0.991508 – 0.992428 | 1.361 | 9.006 | 4.154 | 0.404 |
| 4 | 95 | 0.992428 – 0.993597 | 3.945 | 12.079 | 6.960 | 0.430 |
| 5 | 96 | 0.993597 – 0.994767 | 2.017 | 15.463 | 7.405 | 0.710 |
| 6 | 95 | 0.994767 – 0.995528 | 1.738 | 16.805 | 6.396 | 0.796 |
| 7 | 96 | 0.995528 – 0.996466 | 2.205 | 18.273 | 9.526 | 0.848 |
| 8 | 95 | 0.996466 – 0.997245 | 2.835 | 16.582 | 9.132 | 0.726 |
| 9 | 95 | 0.997245 – 0.997866 | 4.094 | 13.731 | 7.054 | 0.509 |
| 10 (highest `c`) | 97 | 0.997866 – 0.998529 | 2.245 | **19.930** | 7.986 | 0.934 |

- The bottom decile leaves `R` in **24.8%** of its span — not "essentially its whole range" — and
  caps `R` at `5.77`, under a third of the population maximum. The bottom **three** deciles all cap
  `R` below `9.01`.
- Median `R` rises from **2.90** to **7.99**, a factor of `2.8`, essentially monotonically.
- `corr(c, R) = +0.4991` ⟹ **`c` accounts for 25% of `R`'s variance**; mean within-decile variance
  is `7.99` against a total of `11.89`.
- Read the other way: `R > 15` (14 posets) **forces** `c ≥ 0.994228`.

*(Provenance: **the table is the auditor's and is landed verbatim** — where this document and the
audit disagree the audit wins. It was independently re-derived here from the committed
`data/onethird-mg09ea-independent-audit.json`, and **every load-bearing figure reproduces exactly**:
`corr(c,R) = 0.499101`, `corr(c,log R) = 0.536193`, bottom-decile `R ∈ [1.073, 5.770]` with span
share `0.248`, `R > 15` ⟹ `c ≥ 0.9942276` on 14 posets, and mean-within-decile / total variance
`7.994 / 11.892`. The re-derivation differs only in how the 956 classes are cut into deciles — a
`95/96/…` split against the audit's `96/95/…`, one rank either way at each boundary — which moves the
medians of deciles 2, 4, 9 and 10 by at most `0.08` and changes nothing else.)*

**(b) The correlation has the wrong sign — this is the finding.** `corr(c, R) = +0.50`
(`corr(c, log R) = +0.53`). A control inequality of the shape *"higher standard-sector overlap ⟹
smaller required modulus"* would need this negative. At `n = 7` the poset with the **largest**
required modulus has `c = 0.998001` — near the top of the `c` range. The decile table above is a
**strictly stronger** statement of (b) than the correlation coefficient alone, because it shows the
relation is monotone and not the work of a few outliers.

The programme's honest BK-side statement, which mg-4a86's audit correctly identified as *"the slowest
BK mode has `Ω(1)` standard-sector component"*, is therefore **already true and already
insufficient**: it holds with `c ≥ 0.978` unconditionally across the measured population, and the
transfer still needs a modulus of `20` there. The missing ingredient in L1b is not standard
dominance in the overlap sense.

### 6.1 This conclusion is drawn entirely OFF the class L1b quantifies over

> **[Flagged 2026-07-29 by mg-60d3, on mg-09ea §4.2 (F2). The deliverable did not state this and
> should have.]**

L1b as the corpus states it is the **conditional** *all-pairs-frozen ⇒ standard dominance*, and §7
establishes that **no poset in the ensemble satisfies `δ < 1/3`** — every one of the 956 classes
measured here has `δ ∈ [0.359, 0.5]`. So §6 refutes the **unconditional** implication
*high `c` ⟹ small `R`*, which L1b does not assert. **That is the same category error §7 diagnoses in
the corpus, and it applies to this section.**

The document is not uniformly guilty of it: §7 handles the `c` claim correctly (*"the conclusion
`c ≈ 1` already holds without the hypothesis"* is a valid a-fortiori). The gap is specific to the
`R` claim, where **no a-fortiori is available** — `R` being large off-regime says nothing about `R`
in-regime. Ledger claim 20 already carries the honest, `CONDITIONAL` form; §6's prose did not, and
now does.

**What closes the objection, in this document's favour.** The obvious escape — *"but the conditional
picture is fine in-regime"* — is itself measurable in the direction `δ` can be pushed, and mg-09ea
measured it: **`corr(δ, R) = +0.096`** (`corr(δ, log R) = +0.076`), and the eight lowest-`δ` posets
(`δ ≤ 0.3929`) still span `R ∈ [0.99, 6.96]` with median `3.73`, against `5.88` in the `δ = 0.5`
block. So at `n = 7`, **`δ` does not control `R` either** — approaching the regime boundary buys
nothing measurable. This does **not** reach `δ < 1/3`, which by §7's own argument is unreachable at
every `n`; it removes the escape without pretending to test the hypothesis. *(Both figures re-derived
here from the committed audit JSON: `+0.09554 / +0.07576`.)*

---

## §7 — The conditioning hypothesis is empty, and that was never checkable

The picture under test is *"standard dominance holds only in the all-pairs-frozen regime"*, where
all-pairs-frozen means `δ(P) = max_{x∥y} min(p_xy, 1−p_xy) < 1/3`.

**No poset in the entire mg-8b64 ensemble satisfies it.** Across all **1091** committed rows,
`min δ = 1/3` **exactly** — attained, not undercut — and `0` rows have `δ < 1/3`. Restricted to the
`n = 7` enumeration, `min δ = 0.358974`.

This is not a sampling accident. For any poset **with at least one incomparable pair**, `δ(P) < 1/3`
says every incomparable pair has `p_xy ∉ [1/3, 2/3]` — which **is** what it means for `P` to be a
counterexample to the 1/3–2/3 conjecture. The hypothesis is load-bearing and is **not** decoration:
a chain has no incomparable pairs, so `δ = max ∅`, and under any convention making that `< 1/3` a
chain satisfies the regime without being a counterexample (the conjecture is stated for posets that
are not total orders). Chains have `|L(P)| = 1`, no BK dynamics and no content, so this is a vacuity
hole and not a wrong conclusion — but the qualifier belongs in every statement of the reduction,
including the ledger row. **Which conjecture** a witness would refute also needs splitting, and the
two answers are different:

- A `δ < 1/3` witness of **width 3** refutes the width-3 case — the statement this programme exists
  to prove.
- A `δ < 1/3` witness of **width ≥ 4** refutes the **general** 1/3–2/3 conjecture and leaves the
  width-3 case untouched.

So:

- The regime contains **no non-chain poset** at any `n` **unless the general conjecture is false**.
  (`PROVEN` as a reduction — it is definitional.)
- The corpus's *"off-regime"* rows (`δ = 0.500`) and its *"in-regime"* rows (`δ = 0.381`, `0.360`)
  are **both** outside the conditioning hypothesis. The `1/3` boundary separates neither.
- Therefore the "conditional" qualifier was inferred from a `δ = 0.5` vs `δ ≈ 0.37` contrast in
  `λ₂^BK − λ_std`, and then attached to a regime boundary that no measured poset is near.

**This is a limit on what any computation can settle here**, and it is worth stating plainly now
that computation is in scope: the necessity half of the conditional picture — *does* all-pairs-frozen
buy anything — cannot be tested by enumeration at any `n`. The sufficiency half is the only
empirically reachable half, and this document reports that the *conclusion* (`c ≈ 1`) already holds
without the hypothesis.

---

## §8 — Generalisation audit of this document (Appendix A step 4d, run on myself)

> **[This self-audit was run, was genuinely careful, and still missed the defect. Annotated
> 2026-07-29 by mg-60d3, on mg-09ea §4.1/§4.2.]** It correctly identified §5's population claim and
> §6's control-parameter claim as the most general statements here, and it audited both **for scope
> in `n`** — and got both right. It did **not** audit §6(a)'s *inference* (struck; see §0.4 and §6),
> and it did **not** audit §6 for **scope in regime** (§6.1). **Scope has more than one axis, and a
> deliverable's own 4d pass is not sufficient** — the derivation is right, so re-reading the
> derivation cannot find the defect. This is the fifth consecutive deliverable in the arc with sound
> arithmetic and one over-wide generalisation at a new location, and the **first** where the
> document ran 4d on itself; that it still missed is the finding, not the miss. Recorded in
> `STATE.md` Appendix A.

Appendix A records that this arc is four-for-four on sound arithmetic with an over-wide
generalisation, at a **new location each time**, and directs that the most general statement a
deliverable writes be audited first, wherever it sits. The most general statements here are §5's
population claim and §6's control-parameter claim. Audited:

**What is established.**
- `c ∈ [0.978492, 0.998529]` over **all 956** `n = 7` both-connected isomorphism classes, and
  `c ≈ 0.9966` at the three named posets. Scope: `n = 7`, **both-connected** posets — exhaustive
  within that scope.
- `c` does not control `R` **at `n = 7`, on that population**.

**What is NOT established, and must not be read in.**
- **Not "every n = 7 poset".** The sweep covers *both-connected* posets only — those whose
  comparability graph and incomparability graph are **each** connected. Every `n = 7` poset failing
  either condition is unmeasured, and the phrase "at n = 7" must not be used without that
  qualifier.
- **Not "for off-regime posets".** "Off-regime" here means `δ ≥ 1/3`, which is every poset that
  exists (§7). A claim about off-regime posets in general is a claim about all posets, and this is
  `n = 7` only.
- **Not "SD-quant is unconditional".** `n ≤ 6` (mg-4a86) and `n = 7` (here) agree that `c ≥ 0.978`.
  Two adjacent `n` is a **pattern, not a law**, and the asymptotics cut the other way from
  comfort: `dim U ≤ (n−1)²+1` grows polynomially while `|L(P)|` can grow factorially, so `c ≈ 1`
  becomes a *stronger* statement as `n` grows and there is no evidence here that it survives.
- **Not "L1b is dead".** §6 refutes *overlap* as the control parameter on this population. It does
  not show `R` is unbounded in `n` — at `n = 7` the transfer holds with modulus `20`. Whether `R`
  is bounded uniformly in `n` is untouched and remains the open question.
- **Completeness: this one was a caveat and has been closed instead.** `enumerate_both_connected`
  dedups by `iso_signature`, which its own docstring says is *"not a perfect canonical form"* — so
  946 was only a lower bound and some isomorphism classes went unmeasured. The script now
  canonicalises properly (§5.1): there are **956** classes, mg-8b64's dedup dropped **10**, and all
  10 are measured. The population claim covers **every** `n = 7` both-connected isomorphism class.
  This does not extend to non-both-connected posets, which remain outside the sweep.

**Falsification probe against the small-`n` reading.** The corpus's own family/named stress posets
(mg-8b64 `biased_families` + mg-b0a6 `named_posets`, `n` up to 10, including `fence8`,
`triple-ladder n8 w3`, and the `n = 10` LEM-cyclic witness) were measured for the sole purpose of
letting a larger-`n` case falsify the pattern. They are a **locked family**, not a population: they
can break the pattern, they cannot establish it. Results are in the JSON under `families`.

---

## §9 — Consequences for already-merged corpus claims

Each of these is a claim in a merged document that this measurement changes. Named exactly, with
its label there.

| where | the claim | verdict here |
|---|---|---|
| `OneThird-StandardDominance-ComparisonRoute.md` §7.3 | *"Predicted outcome `c ≈ 0`"* at `#600/#3/#20` | **REFUTED.** Measured `0.9966 ± 0.0007`. |
| ibid. §7.3 | *"A genuinely degree-2 slow mode has small overlap with `U`"* | **REFUTED** (Lemma 3.1 + 137 exact witnesses). Invalid inference, not a wrong number. |
| ibid. §7.3 | *"My sweep does not reach those posets, so §7.1 does not contradict them"* | **CONFIRMED and now moot** — the honest caveat was correct; the posets it deferred to agree with §7.1. |
| `OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:302-306` | *"a genuinely slow BK mode exists but it is **non-standard** (degree-2, the lone frozen pair) […] the low-energy cut lands in the wrong irrep"* | **REFUTED as stated.** The slow mode is `99.6%` inside `U`. The *numbers* in that table are reproduced exactly; the irrep-level reading of them is what fails. |
| ibid.:290 | *"Standard dominance is not universal, and the mg-8b64 data pins exactly where it fails and holds"* | **CONFIRMED only under the equality reading** (`λ₂^BK = λ_std`), which mg-4a86's audit already classified as a strawman. Under the overlap reading — the one mg-4a86 identifies as the honest BK-side statement — it does **not** fail off-regime. |
| ibid.:310 | *"So **L1b ⟺ all-pairs-frozen ⇒ standard dominance**"* | **The off-regime half loses its support.** The `⟸` direction was carried by "standard dominance fails off-regime", which is false in the overlap sense. |
| `STATE.md` mg-4a86 row | *"standard dominance appears to hold only in the all-pairs-frozen regime — already indicated by L1b's off-regime n=7 refuters"* | **The stated indication does not hold.** Those refuters have `c ≈ 0.9966`. Also: the regime named is empty in the ensemble (§7). |
| `STATE.md` mg-4a86 row | *"The one uncomputed decisive check (overlap `c` at the 3 known n=7 off-regime posets) is blocked"* | **Discharged.** Computed; result is above. |
| `union_closed/docs/roadmap.md:12` | *"Standard dominance is CONDITIONAL on all-pairs-frozen"* | **Not supported by the overlap form.** Needs re-wording to name which form is conditional. |
| `STATE.md` mg-4a86 row | *"SD-quant overlap `c ≥ 0.979`, n ≤ 6"* | **CONFIRMED and extended** to `c ≥ 0.978492` at `n = 7` across all 956 `n = 7` **both-connected** isomorphism classes. *(The qualifier was added 2026-07-29 — mg-60d3, on mg-09ea §6. §8 is explicit that the sweep covers both-connected posets only; this row, the artifact that outlives the document, had dropped it. It is not optional: every `n = 7` poset failing either connectivity condition is unmeasured.)* |
| mg-8b64 (`onethird_mgb0a6_..._probe.py:enumerate_both_connected`) | its `n=7` both-connected list, 946 posets, used as the enumeration everywhere downstream | **Undercounts by 10** — there are 956 `n = 7` **both-connected** isomorphism classes; `iso_signature` is not a canonical form and collapses 10 of them. No mg-8b64 conclusion turns on the 10 (§5.1). **The site is `docs/OneThird-L1b-BK-Transport-Transfer-Probe.md:86`** — *"Exhaustive both-connected posets **n = 3..7** (3, 9, 12, 104, 946 posets)"* — located by mg-09ea §6 and named here 2026-07-29 (mg-60d3), because *"wrong wherever it is quoted"* is not actionable. **`n ≤ 6` is unaffected:** mg-09ea's generating-function count (`1, 12, 104` at `n = 4, 5, 6`) matches `enumerate_both_connected` exactly, so `iso_signature` is exact below `n = 7` and first collides at `n = 7`. |

**What is NOT changed.** Steps 1–8 of the paper; the `λ₂^BK ≠ λ_std` refutation (C1 antichain, C4
ordinal sums — those are hand proofs and stand); the tempering/deformation route being dead
(C8/C9); the "0/132 is Cayley-walk evidence" catch. None of those depend on `c`.

---

## §10 — Recommendation on the mg-4a86 dataset-revert (report only; pm-onethird's call)

The ticket asks for a recommendation, explicitly not an action. **Recommendation: do not revert.
Keep the epistemic downgrade.** Three reasons, in decreasing strength:

1. **The rule it violated was not in force.** The revert was held pending Daniel's directive call;
   that call has been made, and it says the no-computation directive was scoped to its moment. The
   mg-4a86 datasets are not over-runs against a live rule. Reverting now would enforce a
   prohibition after it was withdrawn.
2. **They are load-bearing for this deliverable.** `scripts/onethird_mg4a86_sdquant_overlap.py` **is**
   the instrument this ticket measures with (CHECK-0 pins agreement at `0.0e+00`), and
   `data/onethird-mg4a86-sdquant-overlap.json` is the `n ≤ 6` baseline the `n = 7` numbers extend.
   Reverting the data while keeping the script leaves a script with no committed baseline;
   reverting the script breaks this document's reproducibility.
3. **A reverted artifact cannot be annotated,** and mg-4a86 §7.3 now needs an annotation (§9). The
   correction is more useful attached to the document than applied by deletion.

**Keep, however, the downgrade that was correct on its own merits.** mg-4a86's enumeration-only
claims (C2 counts, C3-`⟹`, C10 SD-quant) were downgraded to *corroborative* for two distinct
reasons — the guardrail violation, and `feedback_empirical_green_is_not_proven`. Only the first
lapses. **Empirical remains not-proven**, and that applies verbatim to §4–§6 of this document: they
are measurements over a finite population, not theorems.

---

## §11 — Claim ledger

Every claim, including reductions asserted in prose. `PROVEN[c]` = proven by computation
(reproducible from the committed script + data; double-precision `eigh`, with the caveat in §11.1).

| # | claim | label | condition / scope |
|---|---|---|---|
| 1 | `c(#3) = 0.995552`, `c(#20) = 0.996857`, `c(#600) = 0.996549` | **PROVEN[c]** | `c` as pinned in §1.1; uniform measure on `L(P)` |
| 2 | `λ₂^BK` is **simple** at all three, so `c_min = c_max` | **PROVEN[c]** | at tolerances `1e-9` and `1e-6` |
| 3 | Those values exceed the random-subspace null (`0.067/0.111/0.152`) by 6.6–15× | **PROVEN[c]** | null = `dim U/\|L\|`, corroborated by 20 seeded draws (CONTROL D) |
| 4 | The corpus's predicted `c ≈ 0` at these three posets is **refuted** | **PROVEN[c]** | given 1–3; prediction quoted verbatim in §1.2 |
| 5 | The three posets are the ones the corpus names (`\|L\|`, `λ_std`, `δ` **and `λ₂^BK`** match the committed mg-8b64 rows) | **PROVEN[c]** | `\|L\|` exact; `λ_std`, `δ`, `λ₂^BK` to `< 1e-9`. **`λ₂^BK` was fetched but never compared until 2026-07-29 (mg-60d3, on mg-09ea F3); it is now in the gate. The value was always right** — mg-09ea's independent Laplacian route agrees to `≤ 2.5e-15` |
| 6 | **Lemma 3.1**: if `x <_σ y ⟺ pos_σ(x) ≤ k` on all of `L(P)`, then `1[x<_σ y] ∈ U` exactly | **PROVEN** | elementary, no computation; witness family `1 ‖ chain_m` |
| 7 | Hence *"a degree-2 slow mode has small overlap with `U`"* is an **invalid inference** | **PROVEN** | from 6; a single witness suffices to break an inference |
| 8 | The frozen-pair indicator's own overlap with `U` is `≥ 0.779` over the population and **exactly `1` in 137/946** posets | **PROVEN[c]** | mg-8b64's own Theorem-E frozen pair (argmin ratio), not the max-bias pair |
| 8b | Lemma 3.1's threshold hypothesis holds at **137 of those 137** posets | **PROVEN[c]** | so the exact cases are instances of claim 6, not coincidences |
| 8c | `enum-n7-#86` is a **non-vacuous** witness: `dim U/\|L\| = 0.156`, frozen pair `(2,6)`, and `2 <_σ 6 ⟺ pos_σ(2) ≤ 2` on all of `L(P)` | **PROVEN[c]** | matters because the `1‖chain_m` illustration has `U =` the whole space and is vacuous |
| 9 | Over **all 956** `n=7` both-connected isomorphism classes, `c ∈ [0.978492, 0.998529]`, median `0.994751` | **PROVEN[c]** | exhaustive over that class (claim 16); says nothing about non-both-connected posets |
| 10 | `corr(c, δ) = 0.055` — `c` is essentially independent of `δ` | **PROVEN[c]** | computed on the 946-poset sweep block |
| 11 | `R = (1−λ_std)/(1−λ₂^BK)` spans `[0.9923, 19.9303]` while `c` spans a 2%-wide band | **PROVEN[c]** | same scope |
| 12 | Hence `c` does **not** control the L1b transfer at `n = 7`, and `corr(c,R) = +0.50` has the wrong sign for a control inequality | **PROVEN[c]** | **The claim is unchanged and stands as worded** (mg-09ea: CONFIRMED, and strengthened by the decile table). **Its derivation was replaced 2026-07-29 (mg-60d3, on mg-09ea F1): it read "reduction from 9+11", which is INVALID** — claims 9 and 11 are the two range facts and range width is not explanatory power. **It rests on the sign result and the monotone decile table of §6(a′)/(b), not on the widths.** Scope is `n = 7`, this population — **not** a claim about all `n`, and (§6.1) **entirely off L1b's `δ < 1/3` hypothesis class** |
| 13 | No poset in the mg-8b64 ensemble (1091 rows) has `δ < 1/3`; `min δ = 1/3` exactly | **PROVEN[c]** | read from the committed dataset |
| 14 | **For any poset with at least one incomparable pair**, `δ(P) < 1/3` ⟺ `P` is a counterexample to the 1/3–2/3 conjecture; hence the all-pairs-frozen regime contains **no non-chain poset** at any `n` unless the **general** conjecture is false | **PROVEN** | definitional reduction; stated as a reduction, not as evidence. **The hypothesis clause and the width split were restored 2026-07-29 (mg-60d3, on mg-09ea F6): §7's body always had the first, this row had dropped it; `⟹` fails for chains (`δ = max ∅`), a vacuity hole with no effect on the conclusion. A `δ<1/3` witness of width ≥ 4 refutes the general conjecture only** |
| 15 | Therefore the corpus's "off-regime" **and** "in-regime" rows both lie outside the conditioning hypothesis | **PROVEN[c]** | from 13+14 and the quoted `δ` values (0.500 / 0.381 / 0.360) |
| 16 | There are exactly **956** `n=7` both-connected isomorphism classes; mg-8b64's dedup keeps 946 and drops 10 | **PROVEN[c]** | two independent canonicalisations (profile-pruned and brute over all `7!`) agree |
| 16b | The 10 dropped classes give `c ∈ [0.992696, 0.998412]`, so claim 9 is exhaustive | **PROVEN[c]** | — |
| 16c | mg-8b64's reported count of `n=7` both-connected posets undercounts by 10 | **PROVEN[c]** | corrects a merged artifact; no mg-8b64 conclusion turns on it |
| 17 | The instrument can return the correct answer across `c ∈ {0, 0.25, 0.5, 0.75, 1}` to `< 1e-15`, including `c = 0` | **PROVEN[c]** | CONTROL A; synthetic spectrum, answer known in closed form |
| 18 | `c = 1` on antichains is a fact about `U`, not about `dim U` | **PROVEN[c]** | CONTROLS B + C (broken projector returns `0.55/0.29/0.12`) |
| 19 | `c ≈ 1` co-existing with `λ_std ≈ 0.77 ≪ λ₂^BK ≈ 0.98` is a quantitative instance of the static/dynamical category mismatch | **PROVEN[c]** | the mismatch itself was already established qualitatively by mg-4a86's audit; this adds a magnitude, not the phenomenon |
| 20 | The overlap form of standard dominance is *already true and already insufficient* for L1b | **CONDITIONAL** | **conditional on `n = 7` and on this population.** Read as: no `n=7` evidence supports overlap as the mechanism. It is **not** a proof that no overlap-based route can work at large `n` |
| 21 | mg-4a86's `c ≥ 0.979` at `n ≤ 6` extends to `c ≥ 0.978492` at `n = 7` | **PROVEN[c]** | two adjacent `n`; a pattern, **not** a law (§8) |
| 22 | `c ≥ 0.9789` persists on the corpus's family/named stress posets up to `n = 10`, including `fence8` (null `0.026`) and the `n=10` LEM witness (null `0.035`) | **HEURISTIC** | a **locked family**, chosen by the corpus for other reasons; can falsify the pattern, cannot establish it. 10 of the 29 rows are **vacuous** (`dim U = \|L\|`) and are excluded |
| 23 | Recommendation: do not revert the mg-4a86 dataset; keep the epistemic downgrade | **not a claim** | a recommendation; the decision is pm-onethird's |
| 24 | **`c` is substantially informative about `R`** — `corr(c,R) = +0.4991` ⟹ `c` accounts for **25%** of `R`'s variance; the bottom `c`-decile confines `R` to `[1.073, 5.770]` (24.8% of the span) and median `R` rises monotonically `2.90 → 7.99` across deciles; `R > 15` forces `c ≥ 0.994228` | **PROVEN[c]** | **added 2026-07-29 (mg-60d3), landing mg-09ea §4.1. This is what REPLACES the struck §6(a).** Computed on mg-09ea's independent 956-class sweep; re-derived here from `data/onethird-mg09ea-independent-audit.json`. **It strengthens claim 12, it does not weaken it** — the information runs the wrong way for a control inequality. Scope `n = 7`, both-connected |
| 25 | **`δ` does not control `R` either at `n = 7`**: `corr(δ, R) = +0.096` (`corr(δ, log R) = +0.076`); the eight lowest-`δ` classes (`δ ≤ 0.3929`) span `R ∈ [0.99, 6.96]`, median `3.73`, against `5.88` in the `δ = 0.5` block | **PROVEN[c]** | added 2026-07-29 (mg-60d3), landing mg-09ea §4.2. Closes the *"but the conditional picture is fine in-regime"* escape **in this document's favour**. Scope `n = 7`, both-connected; **it does not and cannot reach `δ < 1/3`** (claim 14) |
| 26 | **§6's conclusion is drawn entirely off L1b's hypothesis class** — L1b is the *conditional* all-pairs-frozen ⇒ standard dominance, and every one of the 956 classes measured has `δ ∈ [0.359, 0.5]` | **PROVEN** | added 2026-07-29 (mg-60d3), landing mg-09ea F2. §6 refutes the *unconditional* implication, which L1b does not assert. §7's `c` claim is a valid a-fortiori; **no a-fortiori is available for `R`**. Claim 20 already carried the honest form; §6's prose did not |
| 27 | The CI gate **fires** on both mutations that previously passed it: M1 (BK step rescaled) via `match_bk_lambda2`, M2 (`U` shrunk by element block) via CONTROL B's `c_min`; and neither repair fires on the unmutated instrument | **PROVEN[c]** | added 2026-07-29 (mg-60d3), landing mg-09ea F3/F4. Full 2×3 exit-code matrix in §2.6.1 and `data/onethird-mg60d3-gate-mutation-demo.json`; the demo asserts the matrix and exits non-zero otherwise. **CONFIRMED 2026-07-30 by mg-5ad1** by a disjoint route (real pre-repair source at `87f0424` + source-level mutations). **Scope, as worded: these two mutations.** It is **not** a claim that the gate is mutation-tested in general — mg-5ad1 exhibits two further one-line mutations of the same family that pass it (§2.6.1 annotation) |

### 11.1 The one caveat on every `PROVEN[c]` label

These are double-precision `numpy.linalg.eigh` computations, not exact arithmetic. Three things
bound the risk, and none of them eliminates it:

- CONTROL A returns closed-form-known answers to `≤ 3.3e-16`.
- ~~CHECK-0 agrees with an independently-written instrument to `0.0e+00`.~~ **RESTATED
  2026-07-29 (mg-60d3, on mg-09ea F5): CHECK-0 verifies the wrapper, not the instrument, and bounds
  no numerical risk.** `measure()` and `sd_quant_constant()` call the **same** `bk_walk_matrix` and
  the **same** `projector_U` on the same inputs, and `slow_eigenspace` duplicates the four
  eigenspace-selection lines inside `sd_quant_constant`; identical floating-point operations on
  identical inputs give `0.0e+00` **by construction**. It is invisible to any error in the shared
  code — which is exactly the class of error the two mutations in §2.6 represent. The bullet as
  written contradicted §2.5's own *"not a re-implementation that could differ from it"*. **The
  external agreement that does carry weight is mg-09ea's**, which rebuilt every figure from
  definitions by a disjoint route (own linear-extension enumeration, graph-Laplacian BK operator,
  inverse iteration instead of `eigh`, least-squares `P_U`, exact-`Fraction` `p_xy`) and agrees to
  `≤ 1e-8`, typically `1e-13`.
- Every margin claimed is enormous relative to any plausible numerical error: the smallest is
  `c = 0.9785` against a null of `0.20`, a margin of `0.78` against errors at `1e-15`.

A `PROVEN[c]` label here means "reproducible from the committed artifact and robust by many orders
of magnitude to floating-point error", not "certified by exact arithmetic".

---

## §12 — Reproduction

```
/usr/bin/python3 scripts/onethird_mg2c34_n7_overlap_test.py            # everything; writes the JSON
/usr/bin/python3 scripts/onethird_mg2c34_n7_overlap_test.py --no-sweep # CI control mode; writes nothing
/usr/bin/python3 scripts/onethird_mg60d3_gate_mutation_demo.py         # the gate's own mutation demo (§2.6)
```

**Name the interpreter — `python3` is the wrong one on this host** (mg-09ea F7, landed 2026-07-29
by mg-60d3). The default `python3` here is homebrew 3.14.6 with **no numpy**; only `/usr/bin/python3`
(3.9.6, numpy 1.25.2) runs any of this. CI installs numpy, so the gate is unaffected — but §12 is
the *reproduction* instruction and it did not run as written on the host the work was done on.

Requires `numpy`. Deterministic except CONTROL A/D, which are seeded
(`numpy.random.default_rng(20260729)`). The full mode writes
`data/onethird-mg2c34-n7-overlap.json`; every table in this document is a projection of that file.
`--no-sweep` deliberately does **not** write, so the CI run cannot replace the committed dataset
with a sweep-less copy. Both modes exit non-zero if any control fails (§2.6).

The three posets are recovered by index from `enumerate_both_connected(7)` and their identity
re-verified against the committed mg-8b64 dataset (`|L|`, `λ_std`, `δ`, **`λ₂^BK`**) **before**
anything is measured on them; a mismatch is a hard failure, not a warning.

---

## §13 — Open, and what to ask next

The overlap question is closed at `n = 7` and the answer is not the one the corpus expected. The
question it displaces onto:

**Is `R(P) = (1−λ_std)/(1−λ₂^BK)` bounded uniformly in `n`?** That, not overlap, is what L1b needs.
At `n = 7` it is bounded by `19.93`, and the poset attaining that has `c = 0.998`. The productive
next probe is to characterise `argmax R` structurally and see whether that family's `R` grows with
`n` — a question this document deliberately does not answer, because answering it from a family
chosen at `n = 7` is exactly the locked-parameter error Appendix A step 4d exists to catch.

---

## §14 — The mg-09ea audit, landed (mg-60d3, 2026-07-29)

`docs/OneThird-mg2c34-n7-Overlap-Test-IndependentAudit.md` audited this document independently: it
imported nothing from the corpus and rebuilt every figure from definitions by a disjoint route
(own linear-extension enumeration in a different index order, graph-Laplacian BK operator, shifted
inverse iteration instead of `eigh`, least-squares `P_U` with the transposed column layout, exact
`Fraction` counting for `p_xy`, its own canonical form). **Verdict: OVERSTATED — and the arithmetic
CONFIRMED exhaustively. Not one number in this document is wrong.**

**Where this document and the audit disagree, the audit wins.** This section is the ledger of what
that cost.

### 14.1 What was struck or repaired — five items

| # | site | what changed |
|---|---|---|
| 1 | **§0 point 4 and §6(a)** | The *"no explanatory power"* clause **STRUCK at both sites** — BROKEN, and refuted by this document's own dataset. Replaced by the audit's decile table (§6(a′)). **Ledger claim 12 is KEPT as worded**; only its derivation and this prose failed. |
| 2 | **§9, the 956 row** | *"both-connected"* added — the qualifier §8 insists on and the proposed `STATE.md` row had dropped. |
| 3 | **§7 body + ledger row 14** | The *"at least one incomparable pair"* hypothesis restored to the row (§7's body always had it; `⟹` fails for chains), and the **width-3 / general** conjecture split in the same paragraph. |
| 4 | **§6.1 (new)** | §6's conclusion **flagged as off-class** — no measured poset satisfies L1b's `δ < 1/3` hypothesis — with `corr(δ, R) = +0.096` folded in, which closes the objection **in this document's favour**. |
| 5 | **§9, the undercount row** | `docs/OneThird-L1b-BK-Transport-Transfer-Probe.md:86` **named** as the site of the 946 count, and annotated there. *"Wrong wherever it is quoted"* is not actionable. |

Plus the instrument: **§2.6.1** (the two repaired controls and the demonstration that they fire),
**§11.1** (the *"independently-written instrument"* bullet restated — CHECK-0 verifies the wrapper),
and **§12** (the interpreter named: `/usr/bin/python3`, not `python3`).

### 14.2 What lands UNCHANGED — this is the substance, and most of the document

- **The RED.** `c = 0.995552 / 0.996857 / 0.996549` against a corpus prediction of `c ≈ 0` and a
  random-subspace null of `0.067–0.152`. The prediction the corpus called *"the single
  highest-value follow-on"* is refuted **at the opposite end of the range**. `λ₂` is simple at all
  three, so there is no favourable-reading loophole.
- **The mechanism refutation** — Lemma 3.1, three elementary lines, with its **non-vacuous** witness
  (`enum-n7-#86`, `dim U/|L| = 0.156`) and `137 / 137`. The vacuity of the `1‖chain_m` illustration
  was flagged by this document before anyone else could; the audit calls that discipline exemplary.
- **The population sweep** — all **956** `n = 7` both-connected isomorphism classes — **and the
  completeness correction** that produced it. The audit confirmed 956 **three** times: this
  document's canonicalisation, its own finer one, and a generating-function argument touching no
  poset at all. That third route also localises the defect: `iso_signature` is **exact below
  `n = 7`** and first collides at `n = 7`.
- **The most durable item, and it is a reduction rather than a measurement: the conditioning
  hypothesis of the whole conditional picture is EMPTY BY DEFINITION** (§7). `δ(P) < 1/3` on a
  poset with an incomparable pair *is* what it means to be a counterexample to the 1/3–2/3
  conjecture. **This retires an entire class of future experiments** — the necessity half of the
  conditional picture cannot be tested by enumeration at any `n`, and no computation will change
  that. Record it as a reduction, not as evidence.
- **The load-bearing conclusion, unaffected by anything the audit found:** *the overlap form of
  standard dominance is already true and already insufficient.* It rests on the **coexistence** of
  `c ≥ 0.978` across all 956 classes with a transfer that still needs a modulus of `19.93` — not on
  the struck §6(a).
- **The honest framing of §6, which this document already gave itself and which stands:**
  **relocation, not progress.** §6 replaces *"overlap is the control parameter"* with *"we do not
  know what the control parameter is"*, and the `R` question it displaces onto is **L1b's transfer
  restated — so the crux has not moved.** §13 says exactly this, and the audit's §5 confirms it is
  the right call: §13 names the crux rather than pricing a cheap step below it, and it declines to
  answer it from an `n = 7`-chosen family.

### 14.3 What the audit did *not* find

No merged claim is refuted without being named, labelled and located; every quotation in §1, §3 and
§9 is verbatim and in context; the object/coordinate discipline of §1.3–§1.4 is *"one of the
deliverable's real strengths"*; no claim measured is vacuous, and the one vacuous illustration is
flagged by its author. One footnote in this document's **favour**: §2.4's null `dim U/|L|` is the
right null for CONTROL D's construction but slightly conservative for `U` itself (which contains the
constant, so the honest null is `(dim U − 1)/(|L| − 1) = 0.145` at `#600`, not `0.152`) — the error
**understates** the measured margin.
