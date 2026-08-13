# INDEPENDENT ADVERSARIAL AUDIT — `OneThird-Bbias-Locality-Lemma.md` (mg-a58f), audited under mg-d112

**Auditor:** mg-d112 (polecat `d112`). **I did not author the target.** Target: `docs/OneThird-Bbias-Locality-Lemma.md`,
merged as `f252afb` on `origin/main`, 831 lines, authored under mg-a58f.
**Routing:** to **pm-onethird** as second-line. I have **not** annotated `STATE.md` and have not
reported to Daniel. **Constraint:** paper-and-pencil only; no scripts, no datasets, no delta-engine
calls were run for this audit either (§7 below).

---

## 8. VERDICT (stated first)

> **Overall: CONFIRMED, with two OVERSTATEMENT flags and two cross-doc MISSES.**
>
> **The mathematics survives.** Every `[PROVEN]` claim in the target — 40 ledger rows, boxed and
> in-prose — was independently re-derived and **none is BROKEN**. Critically, the two
> direction-sensitive steps the brief singled out are both used in the **correct** direction:
> Theorem 3.3 uses the *lower* half of Diaconis–Graham (`I ≤ D`, giving an **upper** bound on
> inversions) and Cauchy–Schwarz as `(Σ|d|)² ≤ n·Σd²` (bounding `L1` by `L2`). Reversing either
> would have broken the theorem; neither is reversed. The classic lower-vs-upper conflation that
> mg-8f56 caught in mg-0ed7 Finding 7.5 **is not present here**.
>
> **The four refutations of merged work are SOUND.** I checked each against the verbatim source
> text, not against the target's paraphrase. All four quotations are accurate and none is a
> strawman. Correction 3 (the "tolerates quadratic `E[inv_e]`" regime is empty) is the sharpest and
> is exactly on target: mg-dbd1:289 and mg-8201:25 both advertise the tolerance in a chain that
> *substitutes (B)*, and (B) forces `E[inv_e] = O(n)`.
>
> **Two OVERSTATEMENTS, both in text destined for `STATE.md`** (§4 below). The load-bearing one:
> *"everything the program has attacked since mg-8201 is a strictly-at-least-as-strong surrogate
> for it"* is a **universal that is false** — mg-4a86 (standard-dominance/Wilson comparison),
> mg-210d's (R), and the entropy probes are not LIB surrogates. The body's Finding 3.4 correctly
> restricts to **two** objects; §0 and the proposed `STATE.md` row drop the restriction.
> **pm-onethird must not paste the row verbatim.**
>
> **Two cross-doc MISSES** (§6 below), neither of which breaks a target claim:
> 1. **`STATE.md` line 86 already asserts `λ_std→1 ⟺ LIB ⟺ (B)`.** The target quotes line 102
>    ("logically independent") and never mentions line 86 — which asserts the very implication
>    Theorem 3.3 proves and calls "the largest state-change here". `STATE.md` is **internally
>    inconsistent** (86 vs 102). The target's own §11.5 predicted "a cross-doc miss here is the most
>    likely error in this document." It was right.
> 2. **mg-dbd1 §2.3 (lines 182–184) contains an unflagged inequality-direction error**, and the
>    target's *own witness* `W_m` refutes it. The target reads the passage, quotes the line above it,
>    and declares "Both are correct" — true of what it quotes, but it stops one line short.
>
> **Honest NET.** Real progress, but it is **re-pricing, not new mathematics** — which the target
> itself says. The **RED is cheap and correct**. The **four corrections are the expensive part and
> they hold**, with correction 1 re-priced downward (already half-asserted in `STATE.md`) and
> corrections 3 and 4 carrying the real weight. The **AMBER redirect (EQ) survived my attempt to
> break it**: I ran the target's own §3 re-pricing check against (EQ) — the check it recommends and
> declines to run — and (EQ) does **not** collapse into the wall (§2.4 below). No claimed
> `[PROVEN]` result needs to be withdrawn.

---

## 1. CLAIM LEDGER (exhaustive — boxed results *and* in-prose reductions)

Independently re-derived. `C` = CONFIRMED, `P` = PLAUSIBLE, `B` = BROKEN.

| § | claim | target's label | **my verdict** |
|---|---|---|---|
| 1.2 | STATE.md and mg-0ed7 do not disagree; `(LOC) ≠ (B-bias)`, equivalence unproven | PROVEN by citation | **C** — verified: mg-0ed7:589–593 caveat and mg-0ed7:626 `HEURISTIC` row both exist verbatim |
| 1.3 | currency = control by an absolute constant | PINNING | **C** (a recorded decision, correctly flagged as such) |
| 1.4 | measure is `σ` uniform on `L(P)`, static, **not** `λ₂^BK` | PINNING | **C** — see §5 below; the pinning is correct and load-bearing |
| 1.5 | (H) quantifies over all incomparable pairs; bound uniform in `x, n, P` | PINNING | **C** — verbatim from mg-dbd1 §0 |
| 1.6 | **Obs 1.1** — conditional on 1/3–2/3, frozen class = chains, lemma vacuous | PROVEN conditional | **C** |
| 1.6 | RED-by-counterexample and GREEN-by-verification both unavailable; width ≤ 2 uninformative | PROVEN | **C** |
| 2 | **(F1)** `Σ_x m_x = 2E[inv_e]` | CITED | **C** — re-derived: each incomparable pair counted at both endpoints; comparable pairs contribute 0 since `e ⊇ P` |
| 2 | **(F2)** `1−λ_std ≤ 3E[F]/(n²−1) ≤ 6E[inv]/(n²−1)` | CITED | **C** — verified verbatim at mg-210d `probe-lambda-constant-bound.md:148,406`, tagged `[proven]`, equality at the antichain |
| 2 | **(F4)** LIB ⟺ the transport transfer | CITED, not re-verified | **C as a citation** — LIB-scoping §0 confirmed; correctly marked not-re-verified |
| 2 | **(F5)** mg-8201 retired `E[inv_e]=O(n)` as unnecessary | CITED VERBATIM | **C** — exact match at `ExpectedRank-Certificate.md:127–129`; "structurally unnecessary" at :120 |
| 3.1 | **Identity 3.1** `m_x = E\|σ_{<x} Δ D_x\|` | PROVEN, new | **C** — re-derived. Both containment directions check; the `z ∥ x` step is forced correctly |
| 3.1 | lemma strictly stronger than interface thinness `Δ₁ → 0` | PROVEN | **C** (`O(1)` per cut vs `o(n)` per cut) |
| 3.2 | **Theorem 3.2** `max m_x ≤ C ⟹ E[inv_e] ≤ Cn/2 ⟹ 1−λ_std ≤ 3Cn/(n²−1)` | PROVEN, **headline** | **C** — re-derived; arithmetic `6·(Cn/2)/(n²−1) = 3Cn/(n²−1)` correct; **quantifier order correct** (the identity is per-poset, so even a per-`P` constant works; uniformity is needed only for the uniform conclusion) |
| 3.2 | this is LIB with a `γ`-free constant, stronger than `O(n/γ)` | PROVEN | **C** — `γ ≤ 1/3 < 1` so `O(n) ⊂ O(n/γ)`; LIB-scoping §0 confirms `γ ∈ (0,1/3]` |
| 3.3 | **Theorem 3.3** `E[inv_e] ≤ E[Σ\|disp\|] ≤ √(n·E[Σdisp²])`; **(B) ⟹ `E[inv_e] ≤ Cn`** | PROVEN, **largest state-change** | **C** — see §2.1. Every step re-derived; both direction-sensitive steps correct |
| 3.3 | antichain sanity check `0.25n² ≤ 0.333n² ≤ 0.408n²` | PROVEN by hand | **C** — I recomputed both closed forms from scratch (§2.2); `E[Σ\|disp\|]=(n²−1)/3`, `E[Σdisp²]=n(n²−1)/6`, `1/√6=0.408` ✓ |
| 3.3 | **correction 1**: STATE.md:102 "two faces logically independent" false in one direction | PROVEN | **C as mathematics; MISS in cross-doc** — see §6.1. Sound, but STATE.md:86 already asserts `LIB ⟺ (B)` |
| 3.3 | **correction 2**: mg-dbd1 §2.1 "(B) is weaker than LIB" REFUTED | PROVEN | **C** — quotation verified verbatim at `Spread-Locality.md:146–148`; it *is* a strength claim, and it is backwards |
| 3.3 | **correction 3**: "tolerates quadratic `E[inv_e]`" is vacuous, regime empty | PROVEN | **C, and the strongest of the four** — verified the tolerance is claimed inside a chain that substitutes (B): `Spread-Locality.md:289` and `ExpectedRank-Certificate.md:25,69`. See §6.2 for the one scope caveat |
| 3.3 | **correction 4**: given (B), (A) SPREAD and `Λ=O(1)` are off the critical path | PROVEN | **C** — (A) is `‖r‖²=Ω(n³)` (`Spread-Locality.md:282`, PROVEN there); the (B)→LIB→(F2) route uses neither |
| 3.4 | **Finding 3.4** LIB weakest **of the three** and alone suffices | PROVEN | **C as stated in the body** — but see §4.1: §0 and the STATE.md row drop "of the three" |
| 3.4 | **(LIB-weak)** `E[inv_e] = o(n²)` ⟹ `λ_std → 1` | PROVEN (F2) | **C** — immediate from (F2) |
| 3.4 | under (H), `E[inv_e] < C(n,2)/3` automatically | in-prose | **C** — each of ≤ `C(n,2)` incomparable pairs contributes `< 1/3` |
| 3.4 | limit-vs-rate routing question unresolved in the record | ~~**[OPEN]**~~ **RESOLVED elsewhere** | **C at the time, and correctly left open** — this is the right call, see §4.3. ⚠️ **ANSWERED 2026-07-29 by `mg-88bd` (audited `mg-e35c`) and reconciled back 2026-08-13 (`mg-ae9e`): NEITHER — the operative form is a constant threshold uniform in `n`, `E[inv_e] ≤ (ε/6)(n²−1)` at `ε ≤ ε_dem ≈ 2×10⁻²`. Full disposition in the target document's §14.** |
| 3.4 | LIB = average-form, lemma = max-form of the same quantity | PROVEN (F1) | **C** |
| 4 | **Identity 4.1** `h(x) − rank_e(x) = Σ_{x<_e y} m_{xy} − Σ_{y<_e x} m_{xy}`, **unconditional** | PROVEN | **C** — re-derived both sign cases; the `(H)`-is-unnecessary correction to mg-dcae §5.4 is right |
| 4 | `b_x ≤ m_x`, equality iff mass one-sided | PROVEN | **C** (triangle inequality) |
| 4 | the lossy step is `b_x ≤ m_x` applied *before* the max | PROVEN as diagnosis | **C** — and mg-dcae §5.4 verbatim does exactly this (`Σ_x M_x² ≤ (max M_x)·Σ M_x`) |
| 5.1 | **Theorem 5.1** `max b_x ≤ C₀ ⟹ (B-bias) ≤ 2C₀E[inv_e]`, unconditional | PROVEN | **C** — every step is an upper bound on the target; correct direction for a sufficiency claim |
| 5.2 | **Obs 5.2** `b_x = m_x` at the `e`-extremes; (EQ)\|ₑ₋ₘᵢₙ = negation of mg-dbd1 §3.1's falsifier | PROVEN | **C** — verified against `Spread-Locality.md:191–198`; at the `e`-min `B_x = 0` so `disp = A_x` and `b_x = m_x` ✓ |
| 5.3 | **Theorem 5.3** `max b_x ≤ C₀ ⟹ Λ ≤ 2C₀+1` | PROVEN | **C** — I re-ran the sorting argument looking specifically for the off-by-one the target flags. **There is none.** Both counting steps are tight and the 0-indexing is consistent |
| 5.3 | (EQ) ⟹ `‖r‖² = Θ(n³)`, re-deriving (A) | PROVEN | **C** — `\|h_k − k\| ≤ C₀` perturbs `Σk² = Θ(n³)` by `O(n²)` |
| 5.3 | (EQ) leaves **(B-cov)** as the sole residual | PROVEN | **C** — mg-dbd1's obligation table (`:280–284`) lists exactly (A), (B), (aux) Λ; (B) splits via mg-dcae:519–522 |
| 6.1 | `W_m` exact values (`Pr[z<c_i]`, `rank_e(z)`, `m_{zc_i}`, `m_z`, `E[pos z]`, `b_z`, `b_{c_i}`, `E[inv_e]`) | PROVEN by hand | **C — every one recomputed independently**, see §2.3, including both micro-checks |
| 6.2 | **Theorem 6.2** `W_m`: `max b_x ≤ 1`, `max m_x = Θ(n)`, `E[inv_e] = Θ(n)`; (EQ) ⇏ locality, LIB ⇏ locality | PROVEN | **C** |
| 6.2 | the `δ = 1/2` caveat: separates *quantities*, not frozen-conditional statements | PROVEN, load-bearing | **C, and correctly scoped** — this caveat is the difference between an honest and a dishonest §6, and it is stated plainly, in the theorem, not buried |
| 6.2 | second reading: `W_m` violates (B) by `Θ(n)`, all in the variance term, (B-bias) healthy | PROVEN | **C** — `Var(pos z) = m(m+2)/12` ✓ (uniform on `{0,…,m}`) |
| 6.3 | `C_p ⊕ A_k ⊕ C_p`, `k=⌊√n⌋`: separates LIB from locality but **not** (EQ) from locality | PROVEN by hand | **C** — `m_x = (k−1)/2`, `E[inv] = C(k,2)/2 = Θ(n)`, `b_x = \|(k−1)/2 − (i−1)\| = Θ(√n)` ✓ |
| 7.1 | conditional uniformity on a contiguous window; in-window elements all `∥ x` | PROVEN | **C** |
| 7.1 | **Lemma 7.1** `E[N_x\|τ] ≥ Σ min(i,W−i)/W ≥ (W−1)/4`; locality ⟹ `E[W_x] ≤ 4C+1` | PROVEN, new | **C** — recomputed both parity cases: `Σ min = m²` at `W=2m`, `m(m+1)` at `W=2m+1`; both `≥ W(W−1)/4` ✓ |
| 7.1 | Lemma 7.1 holds with **equality** on `W_m` at `z` | PROVEN | **C** — verified: `W_z ≡ m+1`, no out-of-window inversions, summand `= m_{zc_i}` exactly |
| 7.2 | **Lemma 7.2** `N_x ≤ (W_x−1) + N_{z⁻} + N_{z⁺}` pointwise | PROVEN, new | **C** — the injection is valid; `y = z⁻` is correctly excluded (comparable pairs never invert) |
| 7.2 | Lemma 7.2 closes nothing (recursion vacuous) | PROVEN limitation | **C**, and honestly stated |
| 7.3 | bounded expected windows necessary but **not** sufficient (`C_m ⊔ C_m`) | PROVEN + rate HEURISTIC | **P — label defect**, see §3.1. The *insufficiency* needs unboundedness, which needs the `Θ(√m)` rate that is itself labelled HEURISTIC |
| 8.1 | two-atom law ⟹ lemma false for abstract frozen laws | PROVEN, re-derivation | **C** — `m_x = ε(n−1) → ∞`, credited to STATE.md obstruction 4 ✓ |
| 8.2 | **Obs 8.1** 3-element system ⟹ `m_{xz} ≤ m_{xy} + m_{yz}`; reverse instance vacuous | PROVEN | **C** — re-derived the substitution; the reverse instance gives `m_{xy}+m_{yz} ≤ 1+m_{xz}`, vacuous under (H) since each `m < 1/3` |
| 8.2 | **Cor 8.2** pairwise marginals + 3-element inequalities cannot prove the lemma; subadditivity wrong-signed | PROVEN | **C** — `m ≡ ε` satisfies the system and is realized by §8.1's law |
| 8.3 | **Obs 8.3** `m_x ≤ 2Σ_d m̄_d(x)`; the lemma **is** summable decay | PROVEN | **C** — at most two elements per `e`-distance since `rank_e` is a bijection |
| 8.4 | within-window variance needs `E[W²]`; `E[W²] ≥ (E[W])²` is the wrong direction | PROVEN as stated | **C** — `Var(unif on W) = (W²−1)/12` ✓; correctly *not* claimed as an additional refutation |
| 9 | verdict RED-by-walling + AMBER redirect; three routes untouched; three recommendations withdrawn | PROVEN modulo judgement | **C** |
| 9 | (EQ) "not known to imply LIB" — an **absence**, explicitly not a theorem | **[OPEN/absence]** | **C, and I stress-tested it** — see §2.4. It survives |

**Ledger totals: 47 claims examined, 45 CONFIRMED, 2 PLAUSIBLE (§7.3's insufficiency label; correction 1's novelty pricing), 0 BROKEN.**

---

## 2. RE-DERIVATION (the load-bearing steps, rebuilt from scratch)

### 2.1 Theorem 3.3 — the flashiest claim, therefore audited hardest

Three steps. I checked each independently of the target's prose.

**Step 1 — `inv_e(σ) ≤ Σ_x |disp_σ(x)|` pointwise.** The target itself names this as the place to
attack ("if that step were wrong, Theorem 3.3 and all four corrections collapse, and nothing else in
the document would notice"). It is **correct**. Let `π` be the permutation of `{0,…,n−1}` sending
`rank_e(x) ↦ pos_σ(x)`; it is a bijection because both `e` and `σ` are linear orders on the same
ground set. Then `D(π) = Σ_x |pos_σ(x) − rank_e(x)| = Σ_x |disp_σ(x)|`, and `I(π)` counts pairs whose
`e`-order and `σ`-order disagree. Since `e` and `σ` both extend `P`, a **comparable** pair agrees in
both and contributes `0` to `I(π)`; so `I(π)` counts exactly the inverted incomparable pairs, i.e.
`I(π) = inv_e(σ)`. ✓

**Direction of Diaconis–Graham.** DG (1977) is `I + T ≤ D ≤ 2I`. The target needs `I ≤ D` — the
**left** half — to get an **upper** bound on inversions. It uses exactly that, and calls it "the
lower half", which is the same inequality read as a lower bound on `D`. **This is the correct half.**
Using `D ≤ 2I` instead would give `E[inv] ≥ E[Σ|disp|]/2` and the theorem would collapse. It does not.
mg-dbd1:134 quotes the sandwich in full, and mg-dbd1:137 uses the *other* half (`E[Σ|disp|] ≤ 2E[inv]`)
for its own purposes — so both halves are live in the corpus and picking the wrong one was a real
risk. I did not re-prove DG (a 1977 published result), but I did check its direction is not inverted
by hand on the reversal family: `n=3` gives `I=3, D=4`; `n=5` gives `I=10, D=12`; `n=7` gives
`I=21, D=24`. `I ≤ D` holds and tightens toward equality — consistent with DG and inconsistent with
any reading in which the inequality points the other way. ✓

**Step 2 — Cauchy–Schwarz + Jensen.** `(Σ_x |d_x|)² ≤ n Σ_x d_x²` pointwise (C–S against the all-ones
vector), so `Σ|d_x| ≤ √(n Σ d_x²)`. Taking expectations and using `E[√X] ≤ √(E[X])` (Jensen,
concavity of `√`) gives `E[Σ|d|] ≤ √(n·E[Σd²])`. **Both directions correct.** The classic error here
would be `E[√X] ≥ √(E[X])`; the target does not make it. ✓

**Step 3 — the substitution.** With (B) as `E[Σ_x disp²] ≤ C·E[inv_e]`:
`E[inv] ≤ √(n·C·E[inv])` ⟹ `E[inv]² ≤ Cn·E[inv]` ⟹ `E[inv] ≤ Cn` (trivial if `E[inv] = 0`). ✓

**Is (B) the real (B)? — Yes, and the theorem is robust to the one verbatim discrepancy I found.**
The target states (B) as `E[Σ_x disp²] = O(E[inv_e])`. That matches **mg-dbd1:140** exactly
(*"Lemma (B) asks for the L2 version `E[Σ_x disp²] = O(E[inv_e])`"*) and **mg-8201:29**. But
**`STATE.md`:98 states (B) differently**: `E[Σₓ disp²] = O( E[Σₓ |disp|] )` — footrule on the right,
not inversions. The target does not flag the discrepancy. **It does not matter**, and I verified both
ways:
- `STATE.md`'s (B) ⟹ the target's (B), via DG's *other* half `E[Σ|disp|] ≤ 2E[inv]` (mg-dbd1:137), with constant `2C`.
- `STATE.md`'s (B) implies LIB **directly**: write `D := E[Σ|disp|]`. Then `D ≤ √(n·E[Σdisp²]) ≤ √(nCD)`, so `D ≤ Cn`, and `E[inv] ≤ D ≤ Cn`. Same conclusion, one step shorter.

So **Theorem 3.3 holds under either statement of (B)**. Recorded as a robustness check, not a defect.

### 2.2 The antichain sanity check — recomputed from scratch

`σ` uniform on `S_n`, `e = id`. `Σ_{i,j} |j−i| = 2·C(n+1,3) = n(n²−1)/3`, so
`E[Σ|disp|] = (n²−1)/3` ✓. `Σ_{i,j}(j−i)² = 2nΣj² − 2(Σj)² = n²(n²−1)/6`, so
`E[Σdisp²] = n(n²−1)/6` ✓. Right-hand side `√(n·n(n²−1)/6) ≈ n²/√6 = 0.408n²` ✓.
`E[inv] = C(n,2)/2 ≈ 0.25n²` ✓. Chain `0.25 ≤ 0.333 ≤ 0.408` holds with slack ratios 1.33 and 1.22 —
**tight enough that a sign error would have shown**, as the target claims. ✓

### 2.3 `W_m` — recomputed independently, including both micro-checks (brief item 2)

I did **not** read the target's values; I rebuilt them and then compared.

`W_m = C_m ⊔ C_1`, `n = m+1`, `|L(W_m)| = m+1` (`z` into one of `m+1` slots, uniform). ✓

- `Pr[z <_σ c_i] = i/(m+1)`: `z` precedes `c_i` iff slot `∈ {0,…,i−1}`, `i` of `m+1` slots. ✓
  **`m=1` micro-check, recomputed:** LEs are `zc₁`, `c₁z`. `Pr[z<c₁] = 1/2 = 1/(1+1)` ✓
  **`m=2` micro-check, recomputed:** LEs are `zc₁c₂`, `c₁zc₂`, `c₁c₂z`. `Pr[z<c₁] = 1/3` ✓, `Pr[z<c₂] = 2/3` ✓
- `c_i <_e z ⟺ i < (m+1)/2`, so `rank_e(z) = t`. For `m=2s`: `i ≤ s`, `t = s = ⌈(m−1)/2⌉` ✓. For `m=2s+1`: `i ≤ s`, `t = s = ⌈(m−1)/2⌉` ✓ (at `m` odd, `i=(m+1)/2` is an exact tie; either orientation gives `t=s`).
- `m_{zc_i} = min(i, m+1−i)/(m+1)` — the minority side of `i/(m+1)`. ✓
- `m_z = Σ_i min(i,m+1−i)/(m+1)`. At `m=2s`: `Σ min = 2(1+⋯+s) − s + s = s(s+1)`, so `m_z = s(s+1)/(2s+1) = Θ(m)` ✓.
  **`m=2` micro-check, recomputed:** `m_{zc₁} = min(1,2)/3 = 1/3`, `m_{zc₂} = min(2,1)/3 = 1/3`, sum `2/3`; formula `s(s+1)/(2s+1) = 1·2/3 = 2/3` ✓
- `E[pos_σ(z)] = m/2` (slot uniform on `{0,…,m}`) ✓. `b_z = |m/2 − t| = 0` (`m` even) or `1/2` (`m` odd), so `b_z ≤ 1/2 ≤ 1` ✓ — **the target's `≤ 1` is not tight but is correct.**
  **`m=2` micro-check, recomputed:** `E[pos(z)] = (0+1+2)/3 = 1`, `rank_e(z) = 1`, `b_z = 0` ✓
- `E[pos_σ(c_i)] = (i−1) + i/(m+1)`; `rank_e(c_i) = i−1` (`i ≤ t`) or `i` (`i > t`). So `b_{c_i} = i/(m+1) ≤ 1` or `1 − i/(m+1) ≤ 1` ✓
- `E[inv_e] = Σ_i m_{zc_i} = m_z` ✓, and (F1) cross-checks: `Σ_x m_x = m_z + Σ_i m_{zc_i} = 2m_z = 2E[inv_e]` ✓
- `Var(pos_σ(z)) = ((m+1)²−1)/12 = m(m+2)/12` ✓

**All values confirmed. `max_x b_x ≤ 1` holds, so Theorem 6.2 and the entire AMBER redirect stand.**
Both inline micro-checks are genuinely hand-checkable in under a minute, as claimed; the enumerations
are of 2 and 3 linear extensions.

### 2.4 The check the target recommends and does not run: **does (EQ) re-price into the wall?**

The target says: *"Anyone taking the (EQ) ticket should re-run §3's re-pricing check against (EQ)
first."* Since (EQ) failing this check would void the AMBER redirect, I ran it.

Sum Identity 4.1 over an `e`-prefix `S_j = {x : rank_e(x) < j}`. Since
`Σ_{x∈S_j} pos_σ(x) = C(j,2) + L_j(σ)` where `L_j` counts `e`-inverted pairs crossing cut `j`,
we get `Σ_{x∈S_j}(h(x) − rank_e(x)) = E[L_j]`. Under (EQ) each term is `≤ C₀` in modulus, and the
complementary cut gives the other side, so

> **(EQ) ⟹ `E[L_j] ≤ C₀·min(j, n−j)` for every prefix cut `j`.**

Now `Σ_{j=1}^{n−1} L_j(σ) = Σ_{inverted pairs} (e\text{-distance}) ≥ inv_e(σ)`, so
`E[inv_e] ≤ Σ_j E[L_j] ≤ C₀ Σ_j min(j,n−j) ≈ C₀n²/4`.

**That is `Θ(n²)` — the trivial bound. (EQ) does not deliver LIB by this route**, which is the
natural analogue of Theorems 3.2/3.3. **The redirect survives**, and the target's "not known to imply
LIB" is confirmed as an accurate statement of an absence rather than an unexamined hope. (Offered to
pm-onethird as a free corroboration; the per-cut bound `E[L_j] ≤ C₀ min(j,n−j)` is a genuine
consequence of (EQ) the target did not record.)

---

## 3. LABEL AUDIT

**Clean, with one defect.** Every `[HEURISTIC]`, `[OPEN]`, and conditional item is labelled at the
point of use *and* in §10's ledger, and **no heuristic is promoted into §0**. Specifically:
- Obs 1.1 is conditional on the 1/3–2/3 conjecture and says so in the box. ✓
- §9's "(EQ) not known to imply LIB" is labelled an **absence, explicitly not a theorem**, in §0 (via
  the §6.2 pointer), §9, and the ledger. ✓ This is the item most tempting to upsell, and it is not upsold.
- §7.3's `Θ(√m)` rate is labelled HEURISTIC. ✓

**3.1 The one label defect (minor, PLAUSIBLE not BROKEN).** §7.3's ledger row reads
*"PROVEN for the identity and the insufficiency; the rate `Θ(√m)` is HEURISTIC and carries no load."*
The **insufficiency** claim ("bounded expected windows is necessary but not sufficient") requires
`m_{a_i}` to be **unbounded**, and the target's stated non-heuristic ground for that is
`m_{a_i} = E|K_i − (i−1)| > 0` — but *positivity does not give unboundedness*. The unboundedness
comes only from the `Θ(√m)` rate, which is HEURISTIC. So the rate does carry load after all, and
"PROVEN … for the insufficiency" should read **PLAUSIBLE (rests on the HEURISTIC rate)**.
Consequence: nil — §7.3 is a structural remark in a section explicitly labelled "recorded as
structure, not as progress", and nothing in §0, §3, §5, or §6 depends on it. Recorded for the ledger.

---

## 4. SCOPE CHECK

**4.1 The §0 headline vs the body — OVERSTATEMENT, and it is in the text destined for `STATE.md`.**

The body's boxed **Finding 3.4** is correctly quantified: *"LIB is the weakest of the **three**
sufficient conditions the program has on the table"* — the set being `{locality, (B), LIB}`, which
the document defines and which is the real set for that claim. **That is not a strawman**; I checked
that the target did not shrink the comparison set to make itself look better. It did not.

But **§0 and the proposed `STATE.md` row (line 807) drop the quantifier**:

> *"LIB is the weakest sufficient condition on the table and alone suffices; **everything the program
> has attacked since mg-8201 is a strictly-at-least-as-strong surrogate for it**."*

Two defects in that sentence:

1. *"the weakest sufficient condition on the table"* is **contradicted two sentences later by the
   target itself** ("And LIB is not the floor either — … needs only **(LIB-weak)**"). Self-correcting
   within the same paragraph, so low-severity, but the unqualified clause is what a reader skimming
   §0 will carry away.
2. *"everything the program has attacked since mg-8201 is a strictly-at-least-as-strong surrogate"*
   is a **universal over the program's whole post-mg-8201 activity, and it is false.** Counterexamples
   from the merged record: **mg-4a86** (standard-dominance / Wilson 2004 universal gap comparison
   route) attacks `λ_std` by comparison, not via inversions, and is not a LIB surrogate; **mg-210d**'s
   (R) frozen-density ceiling is a tool, not a sufficient condition; the **entropy probes**
   (mg-61bb, mg-f82f, mg-92e6, mg-e2de) aim at the Kahn–Saks/BFT `0.2764` bound and `δ` directly.
   The defensible claim is the body's: **two** objects — (B) and the locality lemma.

**Action for pm-onethird: do not paste the §12 `STATE.md` row verbatim.** Replace
"everything attacked since mg-8201" with "both objects the (A)+(B) route has attacked since mg-8201
— (B) and the locality lemma", and restore "of the three" to the "weakest" clause. This is a
five-word edit; the mathematics behind the row is sound.

**4.2 Strawman check on the four refutations — PASSED, all four.** I pulled each target statement
from its source before reading the target's characterisation:
- STATE.md:102 — *"The two faces are logically independent; either alone suffices."* The "two faces"
  are indeed **(B) and LIB** (STATE.md:96–100 defines them as the displacement face and the
  inversion face). The refutation hits the real statement, not a stronger one. Note the HTML mirror
  (`state-of-the-wall.html:393`) adds a parenthetical justification — *"(a single deep-crossing
  element separates them)"* — which supports only the **LIB ⇏ (B)** direction. That direction is
  **true** and the target confirms it (§6.2, `W_m`). So the refutation is correctly restricted to
  the other direction, and "false in one direction" is precisely the right phrasing. ✓
- mg-dbd1 §2.1 — quoted verbatim and it is a genuine strength claim. ✓ (The target truncates the
  sentence before *"which DG already delivers in L1"*; the truncation does not change the meaning.)
- mg-dbd1 §0/§5 + mg-8201 §2 — the "tolerates quadratic" advertisement is real and is at
  `Spread-Locality.md:289` and `ExpectedRank-Certificate.md:25,69,240`. ✓
- mg-dcae §7.2 / Prop 5.4 / mg-0ed7 §7.5 / mg-dbd1 §5.1 — all four "recommended it" citations
  verified verbatim. ✓

**4.3 "RED"/"reopens"/"converges" language — no over-read.** The target explicitly refuses three
over-reads it could have made: it does **not** claim the lemma is false, does **not** claim (B) or
(B-cov) is false, does **not** claim any of the three routes is killed, and states in "What this does
and does not kill" that *no mathematics is refuted* — only pricing and framing. I checked that
against the body and it is accurate. The limit-vs-rate question is left **[OPEN]** and routed rather
than silently picked, which is the correct call given (F4) states the equivalence for the **rate**
form while STATE.md's narrative states the **limit** form. **This is the single most disciplined
piece of scoping in the document.**

---

## 5. OBJECT / COORDINATE CHECK — clean

Every claim concerns `λ_std` and `Pr_σ` with **`σ` uniform on `L(P)`**: a static functional of the
stationary measure (`λ_std` is an eigenvalue built from the position matrix `T_P`, cf. mg-210d:162
where `T = J/n` gives `λ_std = 0`). **No dynamical object appears anywhere in the document**, and §1.4
pins this explicitly *before* any proof, correctly citing mg-4a86's audit-corrected `λ₂^BK ≠ λ_std`
and Leake–Lindberg–Oveis Gharan 2025 as the reason a dynamical reading would be attacking an object
that cannot carry the obstruction. **No static/dynamical conflation found.** Given that mg-4a86
landed an audit correction on exactly this confusion, pinning it in §1.4 rather than leaving it
implicit is the right practice and I record it as such.

---

## 6. CROSS-DOC CONSISTENCY — two misses

**6.1 MISS: `STATE.md`:86 already asserts `LIB ⟺ (B)`.**

`STATE.md` ledger row 8 reads:

> `| 8 | **L1b — the wall**: frozen ⟹ λ_std→1 ⟺ LIB ⟺ (B) | **OPEN** | any |`

Taken literally, this **already asserts** the implication `(B) ⟹ LIB` that Theorem 3.3 proves and
that the target calls *"the largest state-change here"* and *"new"*. The target quotes STATE.md:102
and never mentions STATE.md:86 — sixteen lines above it in the same file.

Two consequences, and they point in opposite directions:
- **The novelty claim must be re-priced.** Theorem 3.3 is better described as *supplying the first
  proof of a direction `STATE.md` already asserted without one* than as a new state-change. The
  proof is still new and still worth having — an asserted `⟺` with no argument behind it is exactly
  the kind of thing this program has been burned by.
- **Correction 1 gets stronger, not weaker.** `STATE.md` is **internally inconsistent**: line 86 says
  `LIB ⟺ (B)`, line 102 says the two faces are "logically independent". Those cannot both hold. The
  target refutes line 102; the sharper finding is that the two lines contradict each other and
  **pm-onethird must reconcile both**, not just annotate line 102. Fixing 102 while leaving 86's
  unproven `⟺` in place would leave the reverse direction (`LIB ⟹ (B)`) asserted and unproven — and
  the target's own `W_m` shows it **fails as an inequality between the quantities** (`W_m` satisfies
  LIB and violates (B) by `Θ(n)`), so row 8's `⟺` is defensible only as a frozen-conditional
  statement, where §1.6 makes it vacuous.

**6.2 MISS: an unflagged inequality-direction error in mg-dbd1 §2.3, refuted by the target's own witness.**

The target quotes `Spread-Locality.md:179` and correctly says the displayed chain is right. But
**lines 182–184, immediately following, contain a reverse-direction error the target does not flag**:

> *"and by Jensen `E[disp(x)²] ≥ E[disp(x)]²`, so if any single `m_x = Θ(n)` while `E[inv_e] = Θ(n)`,
> then `E[Σ disp²] ≥ m_x² = Θ(n²)` and **(B) fails by a factor `n`**."*

The step `E[Σ disp²] ≥ m_x²` requires `|E[disp(x)]| ≥ m_x`, i.e. `b_x ≥ m_x`. The only available
relation is **`b_x ≤ m_x`** (the target's own Identity 4.1). **This is the same `b`-vs-`m` conflation
the target diagnoses as "the lossy step" — used here in the opposite direction, where it is not lossy
but invalid.**

**The target's own witness refutes it.** On `W_m`: `m_z = Θ(n)` and `E[inv_e] = Θ(n)`, yet
`Σ_x E[disp_σ(x)]² = Σ_x b_x² ≤ n = Θ(n)`, **not** `Θ(n²)`. The inference fails on precisely the
poset the target constructs. (On `W_m` lemma (B) does fail — but through the *variance* term, which
is not what the quoted argument claims.)

**Why this matters beyond bookkeeping:** mg-dbd1 §3.2 promotes the same conflation into its statement
of the wall — *"Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with `E[inv_e] = O(n)`?"* — and
that "Equivalently" is **not** an equivalence. mg-dbd1 §3.1's falsifier is valid **only at the
`e`-minimal element**, where `B_x = 0` and `b_x = m_x` (which is exactly the target's Observation
5.2). Generalising it from the `e`-min to `max_x` is the invalid step. Since §3.2's question is
mg-dbd1's *"single pin"* and the origin of recommendation 1, this affects how the recommendation
should be recorded as withdrawn: **the recommended target was not merely mis-priced (too strong), it
was also mis-derived as a falsifier (`max_x m_x = Θ(n)` does not falsify (B-bias)).**

The target has every tool needed to catch this — Identity 4.1, Observation 5.2, and `W_m` — and it
gets within one line. **This is a MISS, not an error in the target**: no target claim depends on
mg-dbd1:182–184, and the target's "Both are correct" is true of the display it quotes. Reported so
pm-onethird can annotate mg-dbd1 §2.3/§3.2 in the same pass.

**6.3 Everything else checks out.** All other cross-doc claims verified verbatim: mg-0ed7:589–593 and
:626 (the HEURISTIC equivalence row), mg-dcae:546–548 (Prop 5.4) and :660–664 (the recommendation),
mg-dcae:519–522 ((B-cov)/(B-bias) split), mg-dbd1:282–284 (obligations table, (A) SPREAD **PROVEN**),
mg-dbd1:191–198 (the falsifier), mg-dbd1:245 (`Λ = max_k(w_{k+1}−w_k)` on the **sorted** vector — the
target's Theorem 5.3 addresses the right object), mg-dbd1:232 (the 20 000-trial figure, correctly
cited not re-run), mg-210d:148/406 ((F2), `[proven]`), mg-8201:120/127–129 ((F5), verbatim).
The claim that mg-0ed7 Finding 7.5 is already REFUTED by mg-8f56 is confirmed by commit `912f1b1`.

---

## 7. CONSTRAINT COMPLIANCE — **PASS, verified against the commit**

I verified this against `f252afb` itself, not against the document's sentence.

- `git show --name-status f252afb`: **exactly one file**, `A docs/OneThird-Bbias-Locality-Lemma.md`,
  831 insertions, 0 deletions. **Zero scripts, zero datasets, zero JSON, nothing under `scripts/` or
  `data/`.** Independently confirms the mayor's check.
- **No number in the document requires a machine.** I enumerated every numeric claim and either
  re-derived it in closed form (§2.2, §2.3, Lemma 7.1's `m²`/`m(m+1)` sums, `Var = (W²−1)/12`,
  `m(m+2)/12`) or traced it to a citation that is correctly marked as cited rather than re-run
  (`(n−1)³/1152` from mg-dbd1 §1; `E[inv_e] = 2n/9` on the tight3 tower; the 20 000-trial figure).
  **No table, constant, or enumeration in this document could not have been produced by hand.**
- The only enumerations are of **2 and 3 linear extensions** (`W_1`, `W_2`), which I redid by hand
  in §2.3. Both are correct.
- **This audit ran no computation either**: no scripts, no datasets, no delta-engine calls. Every
  re-derivation above is pencil arithmetic on closed forms and on permutations of size ≤ 7.
  No block-and-report was necessary — nothing in the document required computation to settle.

---

## What pm-onethird should do with this

1. **Accept the mathematics.** All four corrections to merged work are sound. The RED and the AMBER
   redirect both stand. Nothing needs to be withdrawn.
2. **Edit the proposed `STATE.md` row before pasting it** (§4.1) — the "everything attacked since
   mg-8201" universal is false and would otherwise land in the canonical doc.
3. **Reconcile `STATE.md`:86 against `STATE.md`:102** (§6.1), not just annotate 102. Row 8's `⟺` is
   unproven in the `LIB ⟹ (B)` direction and is falsified as an inequality between the quantities by
   the target's own `W_m`.
4. **Annotate mg-dbd1 §2.3 (lines 182–184) and §3.2's "Equivalently"** (§6.2) — a second, independent
   `b`-vs-`m` direction error in merged work, of the same family mg-8f56 caught in mg-0ed7 §7.5, not
   caught by the target.
5. **Downgrade the §7.3 ledger row** from PROVEN to PLAUSIBLE on the insufficiency claim (§3.1). Nil
   consequence.
6. The target's proposed **"Strength check"** addition to the Appendix A template (§9) is, in this
   auditor's judgement, correct and worth adopting — running a proposed hypothesis *forward* before
   pricing it is exactly what would have caught this three arcs ago. I would add a second line to it:
   **"and check the falsifier's quantifier — a falsifier valid at one distinguished element is not
   valid at the max"**, which is §6.2's error and is not covered by the strength check alone.

---

*Audit deliverable for mg-d112. No computation. Routes to pm-onethird as first-line; pm-onethird is
second-line and owns `STATE.md` and the Daniel report.*
