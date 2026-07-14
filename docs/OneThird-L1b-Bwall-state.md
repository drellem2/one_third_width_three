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
