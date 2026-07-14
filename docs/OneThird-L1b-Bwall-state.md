# OneThird L1b (B)-wall — state doc (mg-2acf)

**Work item:** mg-2acf (high). Prove `Cross = O(E[inv_e])` under `(H: δ<1/3)` + width 3
(⇔ close (B) LOCALITY ⇔ close L1b on the λ_std transport-certificate route), **or**
structurally explain the L2-vs-L1 gap.

**READ-FIRST predecessor:** `docs/OneThird-L1b-Spread-Locality.md` (mg-dbd1, commit `8efdac4`).
That doc proved **(A) SPREAD** `‖r‖²=Ω(n³)` and walled **(B) LOCALITY** down to the single
same-element three-point inversion-correlation object
`Cross = Σ_x Σ_{y≠z} ε_{xy} ε_{xz} E[I_{xy} I_{xz}]`.

**Vision check (anti-drift), run first.** M1 = full gap-free width-3 proof; this ticket is on
the λ_std transport-certificate route. This session stays exactly on that route: it operates on
the *same* `Cross` object the certificate localises to, and **sharpens** the wall rather than
drifting. No vision amendment needed. The result does move the residual toward the
"is a heavy per-element crossing realizable?" question, which is *also* the natural pivot hinge
to `project_onethird_algebraic_program_vision` if the residual proves intractable — flagged
below, not acted on.

---

## VERDICT: AMBER — structural reduction + natural tool refuted; single sharpened residual named.

Not PROVEN (the clean closing tool is *false*, see §4). Not RED (no realizability construction;
all evidence points the other way). The session delivers a **qualitative** structural change
(not mere quantitative narrowing), so it clears the STOP-LOSS "asymptotic-AMBER" trap — and then
**stops and reports** per block-and-report, because the sharpened residual is a genuine open
combinatorics question that should get a PM strategic call before more tokens are spent.

**One-line summary of the advance.** The `Cross` obstruction is **not** a three-point / cross-pair
correlation at all: Dilworth (width 3) + Cauchy–Schwarz eliminate every cross term, reducing (B)
to a **two-point, single-element-vs-single-chain** second-moment bound. That per-chain bound is
exactly what log-concavity of a linear-extension slot-count would deliver — but that
log-concavity is **numerically false**. What survives is one sharp realizability question: **can a
single element block-cross a long frozen chain?** — now shown to be the *complete* obstruction,
not merely one candidate falsifier.

---

## 1. The per-element chain decomposition (width 3 does real work)

Relabel by `e`-rank so `erank(x)=x`. `disp_σ(x) = pos_σ(x) − x = Σ_{y≠x} ε_{xy} I_{xy}`; only
incomparable `y` contribute (comparable pairs never `e`-invert). So `disp_σ(x)` is a sum over
`Inc(x)` = the set of elements incomparable to `x`.

**Width-3 structural fact.** If `a,b,c ∈ Inc(x)` were pairwise incomparable then `{x,a,b,c}`
is a 4-antichain, contradicting width 3. Hence `Inc(x)` has width `≤ 2`, and by **Dilworth**
splits into **at most two chains** `Y, Z`.

**Per-chain collapse.** Fix a chain `C = (c_1 <_P … <_P c_p) ⊆ Inc(x)`. Because `C` is a chain,
`{c_i before x}` is nested in `i`, so `slot_C := #{i : c_i before x}` is a threshold. Let
`j_C := #{c_i : c_i <_e x}` (a constant; `e` orders `C` as `P` does). A direct count gives

> **`Σ_{c∈C} ε_{xc} I_{xc} = slot_C − j_C =: S_C`,  and the inversion count of `x` within `C`
> is `|S_C|`.**

Therefore, unconditionally,
```
disp_σ(x) = S_Y + S_Z,   |disp_σ(x)| ≤ |S_Y| + |S_Z|,   invdeg_C(x) = |S_C|.
```

## 2. Cauchy–Schwarz kills the cross term (the 3-point correlation is a red herring)

```
E[disp(x)²] = E[(S_Y+S_Z)²] ≤ 2(E[S_Y²] + E[S_Z²]),      m_x := E[invdeg(x)] = E|S_Y| + E|S_Z|,
```
and `Σ_x m_x = 2 E[inv_e]`. Summing over `x`,
```
Cross = E[Σ_x disp²] − 2E[inv_e] = Σ_x E[disp(x)²] − Σ_x m_x
      ≤ 2 Σ_x (E[S_Y²]+E[S_Z²]) − Σ_x m_x.
```
So **(B) holds if `E[S_C²] = O(E|S_C|)` for every frozen chain `C`** — a *per-chain*,
*single-element-vs-single-chain* statement. The cross-pair term `E[I_{xy}I_{xz}]` with `y∈Y,
z∈Z` — the object mg-f9f4 flagged as needing a new 3-point correlation inequality — never
appears. It is absorbed by the elementary inequality `(a+b)² ≤ 2a²+2b²`.

*(This works for any fixed width `w`: `Inc(x)` splits into `≤ w−1` chains and the constant is
`w−1`. Width 3 gives constant 2; the residual per-chain question is width-independent.)*

## 3. The per-chain bound from a frozen straddle — IF the slot count is log-concave

Let `a_m = Pr[slot_C = m]`, `m=0..p`, and `t_k = Pr[slot_C ≥ j_C + k]`. Applying (H) to the two
chain elements straddling `x`'s `e`-rank:
```
t_0 = Pr[c_{j} before x] > 2/3      (c_j <_e x, a non-inversion),
t_1 = Pr[c_{j+1} before x] < 1/3    (c_{j+1} >_e x, an inversion, frozen).
```
**Suppose** `(a_m)` is log-concave. Then (mini-lemma, 4 lines) the suffix sums `(t_k)` are
log-concave too, so their ratios are non-increasing:
```
t_{k+1}/t_k ≤ t_1/t_0 < (1/3)/(2/3) = 1/2   for all k ≥ 0   ⟹   t_k ≤ t_1 (1/2)^{k-1}.
```
Hence the positive tail obeys `E[S_+²] = Σ_{k≥1}(2k−1)t_k ≤ (1+ρ)/(1−ρ)² · E[S_+] ≤ 6 E[S_+]`
with `ρ = t_1/t_0 < 1/2`; the symmetric lower-tail argument (using the `>2/3` bounds on the
`e`-below side) gives the same. So **`E[S_C²] ≤ 6 E|S_C|`**, and chaining through §2,
`E[Σ disp²] ≤ 24 E[inv_e]`, i.e. **`Cross ≤ 22 E[inv_e]`** — (B) closed, *for any bounded width*.

Both hypotheses are load-bearing and non-vacuous: **δ<1/3** supplies the `t_0>2/3, t_1<1/3`
straddle (without it `ρ→1`, no decay); **width 3** caps the number of chains at 2. Monotonicity
(false, mg-b0a6) is never used. This escapes the FKG/XYZ/Shepp/Fishburn insufficiency because it
is **not a correlation inequality at all** — it is a log-concavity of linear-extension *counts*
(an Aleksandrov–Fenchel / order-polytope-flavoured statement), a categorically different tool.

## 4. …but that log-concavity is FALSE (this is the wall, sharpened)

The slot count has a clean linear-extension form: `a_m = e(P_m)`, where `P_m` is `P` with `x`
inserted into the `m`-th gap of the chain (`c_i < x` for `i≤m`, `x < c_i` for `i>m`). **Brute
force refutes log-concavity of `e(P_m)`** (script `…_endtoend_probe.py`, 68 156 checks, **7 537
violations**). Smallest witnesses, e.g. `a = [1,2,6]` (`2² < 1·6`) at `n=5`, and `[5,10,22]`,
`[15,11,11]`, `[10,4,4]`, `[6,4,8]`. So the natural closing tool of §3 **does not exist**. This
is the same phenomenon that sinks Neggers–Stanley (linear-extension count polynomials are not
real-rooted / not log-concave in general).

**Why the failure is not automatically fatal, but names the residual exactly.** The frozen
straddle forces the distribution to be *unimodal with mode at `j` and each tail carrying `<1/3`
mass*. The only way to make `E[S_C²]/E|S_C| = ω(1)` under that constraint is to smear a tail's
`<1/3` mass across `Θ(p)` slots — i.e. approximate the **block-cross** distribution
```
a ≈ [1−c, 0, 0, …, 0, c]      (x is before the whole chain w.p. 1−c, after all of it w.p. c),
```
which is frozen (at `j=0`: `t_0=1>2/3`, `t_k=c<1/3` ∀k≥1) and has `E[S_C²]/E|S_C| = p`. So:

> **(B) LOCALITY  ⟺  the block-cross is NOT realizable (at scale) as the `x`-vs-`C` slot
> distribution of a uniform LE of a frozen (δ<1/3) width-3 poset.**

This is the ticket's named "bimodal chain-cross," now shown to be the **complete** obstruction
(necessary and sufficient), not just one candidate falsifier — and stripped of the cross-chain
correlation. The exact iff is the per-chain one: **(B) ⟺ `Σ_{x,C} E[S_C²] = O(Σ_{x,C} E|S_C|)`**.
A block-cross of a length-`p` chain has `E[S_C²] = Θ(p·m_C) = Θ(m_C²/c)` (with `m_C = E|S_C| =
pc`), so in the block regime this becomes "the crossing profile is flat — no `ω(1)`-sized family
of elements each block-crossing a `Θ(n)` chain." Width 3 caps *simultaneous* deep crossings
(only 2 chains per element; a shared long chain can be block-crossed by boundedly many
incomparable elements), which is why a **global counting/exchange attack** on this residual — not
a correlation inequality — is the natural next move.

## 5. Numerical checks (this session)

Scripts (reuse the mg-b0a6 `Poset`/LE engine, exact enumeration, deterministic):
- `scripts/onethird_mg2acf_endtoend_probe.py` — **decisive**: `e(P_m) = a_m` consistency
  (0 failures / 68 156) and log-concavity of `e(P_m)` (**7 537 failures** → tool of §3 is false).
- `scripts/onethird_mg2acf_perchain_ratio_probe.py` — per-chain `E[S²]/E|S|` on strictly-frozen
  chains (per-pair δ<1/3) in width-3 posets. **Result: over 61 119 strictly-frozen chains at
  `n≤8`, `max E[S²]/E|S| = 2.000`** — bounded, far under the conservative 6 of §3, and *including
  chains whose slot count is NOT log-concave* (e.g. `a=(157,39,26,13)`, `39²<157·26`, ratio still
  2.0). So in-reach the per-chain bound holds even where the §3 tool fails — the tail simply stays
  short/geometric rather than block-shaped. In-reach chains only reach `p=3`, so this cannot probe
  a `Θ(n)` block-cross (the reach caveat below). A lean re-run is `scripts/onethird_mg2acf_perchain_ratio_lean.py`.
- `scripts/onethird_mg2acf_logconcavity_probe.py` — broad log-concavity sweep (times out at
  60k×all-chains; the end-to-end probe supersedes it).

**Reach caveat (unchanged from mg-dbd1).** Exact LE is `O(n!)` (`n≤9`) and strictly-frozen
width-3 posets are vanishingly rare (0 in 20 000 dense trials). The block-cross needs `p=Θ(n)`,
so its realizability is **doubly out of empirical reach** here; in-reach ratios are evidence, not
proof.

## 6. Status table

| item | statement | status |
|---|---|---|
| §1–2 reduction | `Cross=O(E[inv_e])` ⇔ per-chain `E[S_C²]=O(E|S_C|)` | **PROVEN** (Dilworth + Cauchy–Schwarz; cross term eliminated) |
| §3 conditional | slot log-concave ⟹ `E[S_C²]≤6E|S_C|` ⟹ `Cross≤22E[inv_e]` | **PROVEN conditional** |
| §4 tool | slot count `e(P_m)` log-concave | **FALSE** (numerically refuted) |
| **residual** | block-cross non-realizable in frozen width-3 (⇔ `Σm_x²=O(Σm_x)`) | **OPEN — the single pin** |
| (aux) `Λ=O(1)` | no `O(n)` gap in sorted expected ranks | open, separate (mg-dbd1 §3.4) |

## 7. Recommendations (no tickets filed)

1. **Attack the residual as a global counting bound on the `m_x`**, not as a correlation
   inequality: show frozen width-3 forces `Σ_x m_x² = O(Σ_x m_x)`. The per-chain reduction means
   the adversary must realize a heavy (block) slot-tail for *many* elements simultaneously under
   width 3 — a strong constraint a counting/exchange argument may break.
2. **Or refute** by constructing a frozen width-3 poset whose `e`-min element block-crosses a
   `Θ(n)` chain (an explicit large-`n` family; the small-`n` natural constructions of mg-dbd1 §4
   never froze — δ stayed ≥0.357).
3. **If the residual resists both**, this is the clean pivot hinge to
   `project_onethird_algebraic_program_vision`: the certificate route reduces L1b to exactly one
   realizability question, and its intractability is the documented go/no-go for the pivot.

---

# SESSION 2 (mg-9de3) — dual attack on the block-cross residual

**Work item:** mg-9de3 (high). Prove `Σ_x m_x² = O(Σ_x m_x)` for frozen (δ<1/3) width-3
(⇔ per-chain `E[S_C²]=O(E|S_C|)` ⇔ block-cross non-realizable ⇔ (B) closes), **or** construct a
large-`n` frozen width-3 block-cross (pivot hinge).

**Vision check (anti-drift), run first.** Stayed exactly on the (B)/block-cross residual named by
§4 above; no drift, no vision amendment needed. The dual attack is precisely the pre-committed
go/no-go probe for `project_onethird_algebraic_program_vision`.

## VERDICT: AMBER — DUAL-RESIST → **RED-PIVOT** (pre-committed PM strategic call).

Neither PROVEN nor REFUTED; **both** the counting-bound proof and the large-`n` falsification
resist, and the session delivers **qualitative** structural change (not mere quantitative
narrowing), so it clears the stop-loss "asymptotic-AMBER" trap and then **stops** per the
pre-committed hinge. Weight of evidence **leans toward (B) TRUE** (barrier real, approached from
above, never crossed), but it is unprovable-in-reach and the globally-frozen regime is doubly out
of empirical reach. This is exactly the documented fork: **certificate route vs the algebraic-program
vision** — escalated to Daniel (mailed `human`).

## S2.1 The decisive numerics (fast `O(2^n)` LE-count DP breaks the `n≤9` ceiling)

The mgb0a6 engine's ideal-DP (`linext_count`, `before_prob_dp`) computes exact slot
distributions `a_m = e(P_m)/e(P)` and pairwise biases in `O(2^n)`, not `O(n!)` — so `n` reaches
~13 by random search and ~18 by directed gadget. Three findings **correct and sharpen** mg-2acf's
"max ratio ≡ 2.0" (an `n≤8` artifact):

1. **The per-chain ratio is NOT bounded by 2 — it climbs.** Growth curve, max **chain-frozen**
   `E[S²]/E|S|` by `n` (`scripts/onethird_mg9de3_growth_probe.py`):
   ```
   n:      6    7    8    9    10   11    12    13
   ratio:  1.5  2.0  2.0  2.5  2.6  2.90  3.00  3.15   (p capped at 5; chain-δ ~0.28–0.32)
   ```
   The climb tracks the achievable chain length `p` (random search caps `p≤5` at reachable `n`);
   the top shape is a spike-plus-tail `a≈[.023,.045,.068,.068,.081,.715]` (a partial block-cross)
   whose tail is nearly **flat** near the spike (`.081,.068,.068` — ratios ~0.84,1.0) before
   decaying. Whether the flat region **extends with `p`** (ratio→∞) or stays bounded is the pin.

2. **CHAIN-frozen ≫ WHOLE-POSET frozen — and the block-cross needs the latter.** Requiring the
   *whole poset* δ<1/3 (the actual hypothesis H), **no** block-cross appears. Directed
   constructions (mine `scripts/onethird_mg9de3_pscale.py`, plus the hunt-series) push the ratio
   linearly in `p` (flat slot ⇒ `ratio≈p/2`: p=4→12 gives ratio 1.67→**4.43**), but **whole-poset
   δ stays pinned at 0.44–0.49 the entire way, never below 1/3.** The ratio-3.15 growth-curve
   configs are only *chain*-frozen; those posets are **not** whole-poset frozen. Best whole-poset
   δ ever seen for a block-cross is mg-dbd1's **0.357** — thin above 1/3 but never crossed. The
   min-δ-vs-`p` floor sits at **0.44–0.49** and approaches 1/3 **from above**, no dip below.

3. **The robust tension, quantified.** block-cross ⇔ flat/spread slot distribution ⇔ some pair
   straddles Pr≈1/2 ⇔ δ→1/2. Freezing forces a *peaked* slot ⇔ ratio capped. The two requirements
   pull apart at every `p`; nothing achieves frozen **and** diverging-ratio, but nothing proves
   they are strictly incompatible.

## S2.2 New structural results (the qualitative advance)

- **`a_m = e(P_m) > 0` for every gap `m`.** Since `x` is incomparable to every chain element,
  inserting `x` into any gap is order-consistent, so the slot count is strictly positive
  everywhere. Hence the **exact** block-cross (zero interior mass) is *never* realizable; only an
  *approximate* (exponentially-thin-interior) one could give ratio `ω(1)`.

- **Frozen ⟹ a dominant-mode atom `a_j > 1/3`.** Every pair being frozen means every tail
  probability `t_k = Pr[slot≥k] ∉ [1/3, 2/3]`; `t_k` is decreasing, so it jumps from `>2/3` to
  `<1/3` in a single step at `k*=j`, giving `a_j = t_j − t_{j+1} > 1/3`. So a frozen slot
  distribution has one atom carrying `>1/3` of the mass at the correct position `j`. **This does
  NOT close (B):** the block-cross `a=[1−c,0,…,0,c]` has atom `a_0>2/3` yet ratio `p`. The residual
  is whether the remaining `<1/3` tail mass can be pushed to the **far** end (`slot=p`, block) or
  must stay geometric near the mode.

- **The obstruction is a *realizability* constraint on `e(P_m)`, strictly weaker than
  log-concavity (which is refuted).** Purely as probability vectors, frozen U-shaped / block
  distributions exist (e.g. `a=(0.7,0.1,0.2)` is a frozen U-shape on the simplex); what forbids
  them is `a=e(P_m)` for an actual width-3 poset. Neither the frozen constraints nor the simplex
  exclude the block-cross — only realizability does, and it is *not* captured by log-concavity
  (Neggers–Stanley non-real-rootedness, §4). This is the precise, still-open crux.

## S2.3 Why both directions resist (name the dual block, per stop-loss)

- **Proof blocked:** the only clean closing tool (slot log-concavity, §3) is false; the residual is
  a realizability property of `e(P_m)` sequences under width 3 with no known handle short of a new
  poset-LE-counting theorem. `Σ_x m_x²=O(Σ_x m_x)` cannot be forced by the frozen straddle alone
  (the block-cross satisfies every per-pair frozen constraint).
- **Refutation blocked:** every directed block-cross construction is pinned at whole-poset δ ≥
  0.357 (mg-dbd1) / 0.44–0.49 (this session), approaching 1/3 from above but never crossing;
  and the regime that could break it (`p=Θ(n)`, globally-frozen width-3) is doubly out of reach —
  such posets are vanishingly rare (0 in 20 000 random dense trials, mg-dbd1) and a block-cross
  needs `p=Θ(n)`.

## S2.4 Status table (session 2)

| item | statement | status |
|---|---|---|
| per-chain ratio bounded by 2 | mg-2acf impression | **CORRECTED** — climbs to 3.15 (chain-frozen, n=13) / 4.43 (directed, δ≈0.49) |
| `a_m=e(P_m)>0` ∀m | exact block-cross impossible | **PROVEN** (incomparability ⇒ every gap consistent) |
| frozen ⟹ `a_j>1/3` | dominant-mode atom | **PROVEN** (frozen ⇒ `t_k∉[1/3,2/3]` + monotone ⇒ single step) |
| whole-poset-frozen block-cross | δ<1/3 width-3, ratio→∞ | **NOT FOUND** — min δ floor 0.44–0.49, mg-dbd1 0.357, never <1/3 |
| **residual** | approx block-cross non-realizable ⇔ `e(P_m)` far-tail forbidden under width-3 | **OPEN — DUAL-RESIST** (realizability, strictly weaker than refuted log-concavity) |

## S2.5 Recommendation (pre-committed pivot; no tickets filed)

Per the mg-9de3 stop-loss: **declare RED-PIVOT and stop for a PM strategic call.** The certificate
route has reduced L1b (B) to exactly one realizability question whose proof needs a new
poset-LE-counting theorem (log-concavity dead) and whose refutation is blocked by a robust
δ≥0.357-from-above barrier and the doubly-out-of-reach globally-frozen regime. The evidence leans
(B)-TRUE but neither direction is closeable in-reach. This is the documented go/no-go fork:
**continue the certificate route (invest in the realizability theorem) vs pivot to
`project_onethird_algebraic_program_vision`.** Escalated to Daniel. New scripts:
`onethird_mg9de3_{gadget_probe,ushape_probe,ushape_chainfrozen,growth_probe,pscale}.py` and the
`blockcross_hunt*` series.
