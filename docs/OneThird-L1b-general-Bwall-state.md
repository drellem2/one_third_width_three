# OneThird L1b (B) at ANY WIDTH — global chain-counting reformulation + named width-free residual

**Work item:** mg-a7c5 (high, PRIORITY-1, Daniel-released 2026-07-14 option (a) "re-scope-general").
Spectral / near-ordinal-sum program (`spectral_near_ordinal_sum_program.tex`), the **any-width**
baseline. LaTeX-first, prove-or-wall, block-and-report.

> **⚠ mg-0508 UPDATE (successor to mg-a7c5; see §8).** Attacked the single named residual — the
> width-free geometric far-tail decay `E[M_{k,l}] ≤ Cρ^{l−k}E[K_k]` — via a **global/joint**
> argument. Outcome: the residual is **crystallized** to its sharpest form (a *conditional
> threshold-contraction* `ρ_i ≤ ρ<1` for a single element vs an incomparable chain, via chain-nesting)
> and the "pinned above 1/3" evidence is **reproduced and extended to width > 3** with a new
> **freezing-frontier** experiment. **Verdict: AMBER, same family (tail-decay / realizability) as
> a7c5 — this is the SECOND consecutive AMBER in that family, so the mg-0508 trip-wire is FIRED:
> surfaced to PM before any third iteration. NOT PROVEN, NOT RED.** The joint tools (Shepp XYZ, FKG)
> push the *wrong* way and the natural closing tool (slot-law log-concavity) is dead (mg-2acf).

**READ-FIRST predecessors:**
- `spectral_near_ordinal_sum_program.tex` — the any-width baseline (no width bound anywhere;
  `grep -i width` = 0 hits over 603 lines; every L-lemma stated for a general finite minimal
  counterexample).
- `docs/OneThird-L1b-DriftAudit.md` (mg-c899, `042f28c`) — drift diagnosis: the L1b arc silently
  narrowed to width 3 at mg-8201; **(A) is fully general**, the **only** width-3 crutch is the (B)
  aggregation step (Dilworth split of `Inc(x)` into `≤2` chains + constant-2 Cauchy–Schwarz).
- `docs/OneThird-L1b-Spread-Locality.md` (mg-dbd1, `8efdac4`) — **(A) SPREAD** `‖r‖²=Ω(n³)` PROVEN
  (uses only `δ<1/3`, no width), **(B) LOCALITY** walled.
- `docs/OneThird-L1b-Bwall-state.md` (mg-2acf `3692f35` + mg-9de3 `e04d92b`) — the width-3 (B) wall:
  per-chain `E[S_C²]=O(E|S_C|)` residual, log-concavity tool **refuted**, block-cross realizability
  **DUAL-RESIST / RED-PIVOT**.

---

## VERDICT: **AMBER** — width-free global reformulation delivered; **the ≤2-chain Cauchy–Schwarz crutch is removed entirely**; single width-free residual named. Route type-checks at any width up to one realizability theorem.

**What is new and solid (the deliverable).** (B) LOCALITY is reformulated by an **exact,
hypothesis-free, width-free permutation identity** into a **global block-crossing count** — with
**no per-element chain decomposition and no width-dependent aggregation constant**:

> **(GID)**  `Σ_x disp_σ(x)²  =  2 Σ_m K_m(σ)  +  2 Σ_{k<l} M_{k,l}(σ)`  (every σ, every width),
>
> whence, using Diaconis–Graham `Σ_m K_m ≤ inv_e` (also exact),
>
> **(B)  ⟺  `Σ_{k<l} E[M_{k,l}] = O(E[inv_e])`**,
>
> where `K_m` = leakage across cut `m` and `M_{k,l}` = number of elements whose displacement
> interval spans **both** cuts `k` and `l` (a **block-cross** of the whole block `(k,l]`).

This is a genuine improvement on the width-3 route, on two counts: (i) it is an **iff with no lossy
constant** — the mg-2acf per-chain reduction pays an aggregation factor `w−1 = Θ(n)` that **breaks
the sufficient condition itself at unbounded width**; (GID) has no such factor; (ii) it replaces the
per-element/per-chain question by one **global** telescoping quantity, whose natural sufficient
condition is a clean **uniform geometric far-tail decay** `E[M_{k,l}] ≲ ρ^{\,l-k} E[K_k]`.

**Why it does not close (the honest wall).** `Σ_{k<l} E[M_{k,l}] = O(E[inv_e])` reduces to the
**same block-cross realizability question** that was DUAL-RESIST at width 3, now stated width-free:
per-pair freezing (`δ<1/3`) provably does **not** force the required tail decay (the flat-tail
block-cross `a ≈ [1−c, 0,…,0, c]`, `c<1/3`, satisfies **every** frozen pairwise constraint), and a
**single** element block-crossing a `Θ(n)` interval already makes the ratio `Θ(n)` — so no global
"competition for space" cancellation can rescue it. Closing (B) at any width needs a **poset
linear-extension realizability theorem** (that such a block-cross cannot occur under whole-poset
`δ<1/3`), which is exactly the theorem mg-9de3 RED-pivoted on. **Strategic flag:** the certificate
route's viability at the width the `.tex` targets hinges entirely on this one realizability theorem
— a Daniel-level go/no-go (see §7).

**Non-triviality guard satisfied.** (GID) is verified width-agnostically (200 000 random perms, 0
violations; exact on width-4 and width-5 LE ensembles); the block-cross residual object is exhibited
verbatim at **width 4** (an element incomparable to a 3-chain, near-flat slot distribution). Nothing
in the argument references or reintroduces a width bound. Script:
`scripts/onethird_mga7c5_global_chaincount_probe.py`.

---

## 0. Setup (recalled; notation fixed once — reuse from the certificate, unchanged)

`P` a finite poset on `[n]`, uniform linear extensions `L(P)`, `σ ∈ L(P)` a bijection
positions → elements, `pos_σ(x)` the 0-indexed position of element `x`.

**Frozen-counterexample hypothesis (H).** There is a linear extension `e` of `P` (the distinguished
order, `.tex` §1) with every incomparable pair `{x,y}`, `x <_e y`, having
`Pr[pos_σ(x) < pos_σ(y)] > 2/3` (i.e. `δ(P) < 1/3`, majority orientation acyclic and realized by
`e`). **Relabel by `e`-rank**, so `erank(x) = x` and `e = 12⋯n`. Comparable pairs never `e`-invert.
**No width hypothesis is imposed** — this is the whole point of the re-scope.

Certificate quantities (`.tex` §7, §9; mg-8201):
```
u_a = a − (n−1)/2,   r = T_P u,   r_x = E[pos_σ(x)] − (n−1)/2,
disp_σ(x) = pos_σ(x) − erank(x),        inv_e(σ) = # e-inversions of σ,
1 − R(r) = energy(r)/‖r‖²,   energy(r) ≤ ½ Λ² E[Σ_x disp_σ(x)²]   (Λ = O(1) aux, §3.4 of mg-dbd1).
```
Closing L1b via `r` needs the two width-free factors
> **(A) SPREAD** `‖r‖² = Ω(n³)` — **PROVEN and fully general** (mg-dbd1 §1; uses only (H), no width).
> **Reused verbatim; not re-derived here.**
> **(B) LOCALITY** `E[Σ_x disp_σ(x)²] = O(E[inv_e])` — the object of this ticket.

---

## 1. The global chain-counting reformulation (removes the width-3 crutch)

### 1.1 Cut leakage and block-crossings (width-free objects)

Label ranks/positions by `e`. For `1 ≤ m ≤ n−1` the **cut** `m` separates ranks `{1,…,m}` from
`{m+1,…,n}`. Define
```
K_m(σ) = #{x : erank(x) ≤ m,  pos_σ(x) > m}          (leakage across cut m; .tex §5),
```
the number of prefix elements pushed into the suffix. (By bijectivity this equals the number of
suffix elements pulled into the prefix, so the **total** number of elements crossing cut `m` in
either direction is `2K_m`.)

An element `x` **crosses cut `m`** iff exactly one of `erank(x), pos_σ(x)` is `≤ m`; equivalently
`min(erank(x),pos_σ(x)) ≤ m < max(erank(x),pos_σ(x))`. The number of cuts `x` crosses is exactly
`|disp_σ(x)|`. For `k < l`, define the **block-cross count**
```
M_{k,l}(σ) = #{x : x crosses BOTH cut k and cut l}
           = #{x : x's displacement interval [min,max) ⊇ [k,l]}.
```
So `M_{k,l}` counts elements that jump across the **entire** block `(k,l]`. `M_{m,m} = 2K_m`.

### 1.2 The exact identity (GID) — one line, no width, no hypothesis

For a fixed `σ`, `|disp_σ(x)|` = (# cuts `x` crosses), so
`disp_σ(x)² = |disp_σ(x)|² = |disp| + 2·C(|disp|,2)` counts the crossed cuts with multiplicity:
the diagonal `|disp|` counts each crossed cut once, and `2·C(|disp|,2)` counts each unordered pair
of crossed cuts twice. Summing over `x` and reindexing by cut-pairs,
```
Σ_x disp_σ(x)²  =  Σ_x |disp_σ(x)|  +  2 Σ_x C(|disp_σ(x)|, 2)
              =  Σ_m (#x crossing cut m)  +  2 Σ_{k<l} (#x crossing both k and l)
              =  2 Σ_m K_m(σ)  +  2 Σ_{k<l} M_{k,l}(σ).                                   (GID)
```
This is a pure permutation identity — **it holds at every width and needs no hypothesis**.
(Verified: 200 000 random permutations, 0 violations, `n ≤ 12`; exact on width-4/5 poset ensembles.)

### 1.3 The reformulation of (B)

The Diaconis–Graham inequality gives, pointwise, `Σ_m K_m(σ) ≤ inv_e(σ)` (indeed
`Σ_x|disp| = 2Σ_m K_m = D(σ) ≤ 2 inv_e(σ)`; also `inv_e ≤ 2Σ_m K_m`, so `E[inv_e] ≍ E[Σ_m K_m]`).
Taking `E` over `L(P)` in (GID),
```
E[Σ_x disp²]  =  2 E[Σ_m K_m]  +  2 Σ_{k<l} E[M_{k,l}],
```
the first term is `Θ(E[inv_e])` unconditionally, so
> **(B) LOCALITY  ⟺  `Σ_{k<l} E[M_{k,l}]  =  O(E[inv_e])`.**    (★global)

**No `Inc(x)` is decomposed into chains; no per-element constant `w−1` appears.** The width-3
Dilworth+Cauchy–Schwarz step of mg-2acf is **gone**. This is the ticket's requested "global
chain-counting / exchange bound on `Σ_x E[disp²]` that does not decompose each `Inc(x)` into `O(1)`
chains," realized exactly.

### 1.4 Why (★global) strictly improves the per-chain route

- **The per-chain reduction is *broken* at large width, not merely open.** mg-2acf proved
  `(B) ⟸ [∀ frozen chain C: E[S_C²] = O(E|S_C|)]` **via** `disp(x)=Σ_{j≤w−1}S_{C_j}` and
  `(Σ_j S_j)² ≤ (w−1)Σ_j S_j²`. That implication carries a factor `w−1`; at `w = Θ(n)` it reads
  `E[Σdisp²] ≤ Θ(n)·Σ_x Σ_C E[S_C²]`, which is a **factor `n` too weak** to deliver `O(E[inv])`.
  So even a *perfect* per-chain bound would **not** close (B) at unbounded width.
- **(★global) is an exact iff with no such loss.** `Σ_{k<l}E[M_{k,l}]` is a single width-free
  quantity; there is no aggregation constant to blow up. This is the concrete sense in which the
  re-scope is progress: the certificate chain now *type-checks* at the width the `.tex` targets,
  reduced to one clean object.

---

## 2. Attempting to close (★global) — the width-free bounds that are available

Write `P_{k,l} := Pr[\text{a fixed } x \text{ block-crosses } (k,l]]` so `E[M_{k,l}] = Σ_x P_{k,l}(x)`.

### 2.1 Leakage-envelope bound (true but too lossy)

A block-crosser of `(k,l]` crosses **every** cut `m ∈ [k,l]`, hence is counted in every `K_m`:
```
M_{k,l}(σ) ≤ 2 · min_{k ≤ m ≤ l} K_m(σ).                                     (envelope)
```
This is sharp for a *spike* leakage profile (`K_m = n·1[m=m_0]`): then `min_{[k,l]}K_m = 0` for any
`l>k`, so `Σ_{k<l}M_{k,l}=0` and `Σdisp² = 2Σ_m K_m = O(inv)` — the good case. But for a **flat**
profile (`K_m ≡ c`) the envelope gives `Σ_{k<l}2c = Θ(cn²)` against `Σ_m K_m = cn` — a factor `n`.
The envelope over-counts because a flat *leakage* profile does **not** imply flat *spanning* (many
short adjacent crossings give flat `K` with `M_{k,l}=0` for `l>k`). So (envelope) alone cannot close
(★global): the true content is **spanning**, not per-cut leakage.

### 2.2 The sufficient condition: uniform geometric far-tail decay

`Σ_{k<l} E[M_{k,l}] = O(E[inv])` **holds** if there are constants `C, ρ<1` with
```
E[M_{k,l}] ≤ C ρ^{\,l−k} E[K_k]   for all k<l.                               (decay)
```
Indeed then `Σ_{l>k} E[M_{k,l}] ≤ C E[K_k]/(1−ρ)` and `Σ_k` gives `O(E[Σ_m K_m]) = O(E[inv])`. So
> **(decay) ⟹ (★global) ⟹ (B) at any width.**

(decay) is the width-free replacement target for the (refuted) per-chain log-concavity of mg-2acf §3.

### 2.3 Why (decay) does not follow from freezing — the wall, width-free

`E[M_{k,l}]/E[K_k]` is a conditional deep-crossing probability: given an element crosses cut `k`,
how likely is it to reach past cut `l`. Freezing bounds each *single-pair* inversion by `<1/3`, but
the crossing events along a chain are a **nested threshold** (crossing the far cut ⟹ crossing the
near ones), so they do **not** multiply. Concretely, take `x` incomparable to a chain
`C = c_1 <_P ⋯ <_P c_p` with `x` `e`-below all of `C`; `t_s := Pr[c_s \text{ before } x]` is
decreasing and freezing forces only `t_1,…,t_p ∈ [0,1/3)` (each `c_s` `e`-above `x`), which
**permits a flat tail** `t_1 ≈ t_p ≈ c` — the **block-cross** slot law
```
a ≈ [1−c, 0, …, 0, c]   (x before all of C w.p. 1−c > 2/3;  after all of C w.p. c < 1/3),
```
satisfying **every** frozen pairwise constraint yet giving `E[M]` **flat** in the block length (no
`ρ<1`). This is width-independent: `Inc(x)` contains arbitrarily long chains already at width 3, so
the block-cross object is **literally the same at every width**; width changes only the *aggregation*
(≤ `w−1` chains per element), which (★global) has now removed. Hence (decay) — and (★global) — reduce
to the **realizability** question below, unchanged from width 3.

### 2.4 No global cancellation rescue

One might hope the *global* sum enjoys cancellation the per-chain view lacks (block-crosses
"competing for space"). It does not: a **single** element block-crossing a `Θ(n)` interval already
contributes `C(Θ(n),2) = Θ(n²)` to `Σ_{k<l}M_{k,l}` while costing only `Θ(n)` inversions, so
`Σdisp²/inv = Θ(n)` from that one element. No aggregate cancellation over the other elements can
undo a single realized deep block-cross. Thus **(★global) fails iff a single frozen deep block-cross
is realizable** — exactly the mg-2acf/mg-9de3 residual, now width-free.

---

## 3. The residual, named (width-free)

> **RESIDUAL (width-free block-cross realizability).** For a whole-poset frozen (`δ<1/3`) minimal
> counterexample `P` (any width), is there an element `x` and a length-`p = Θ(n)` chain
> `C ⊆ Inc(x)` such that, under uniform `L(P)`, `x` block-crosses `C` (slot law with `Θ(1)` mass at
> the far end) — equivalently `Σ_{k<l} E[M_{k,l}] = ω(E[inv_e])`?
>
> **(B) at any width holds  ⟺  NO such block-cross exists  ⟺  (decay) holds for some `ρ<1`.**

This is **identical** to the width-3 residual of mg-2acf §4 / mg-9de3 (the block-cross object is
width-independent), now correctly attached to the **general** program with the width-3 aggregation
crutch removed. Its status, inherited and re-confirmed width-free:

- **Proof side blocked.** The only clean closing tool (slot log-concavity ⟹ geometric tail) is
  **numerically false** (mg-2acf §4: 7 537 violations of log-concavity of `e(P_m)`;
  Neggers–Stanley non-real-rootedness). Per-pair freezing alone cannot force (decay) (§2.3).
- **Refutation side blocked.** Every directed block-cross construction is pinned at whole-poset
  `δ ≥ 0.357` (mg-dbd1) / `0.44–0.49` (mg-9de3), approaching `1/3` **from above**, never crossing;
  and the globally-frozen `p=Θ(n)` regime is doubly out of empirical reach (strictly-frozen
  width-`w` posets are vanishingly rare, `0` in `20 000` dense trials). Weight of evidence **leans
  (B)-TRUE**, unprovable in reach.

---

## 4. Non-triviality: the argument survives at width > 3 (drift guard)

Per the FORBID clause (no width bound load-bearing; sanity-check at width > 3):

- **(GID) and (★global) are width-agnostic identities** — verified on **exact** LE ensembles at
  **width 4 and width 5** (script §[2]): `E[Σdisp²] = 2E[Σ_m K_m] + 2Σ_{k<l}E[M_{k,l}]` to the last
  rational digit, ratios `E[Σdisp²]/E[inv] ∈ [4.5, 5.6]` (small-`n`, not strictly frozen).
- **The residual object appears verbatim at width 4** (script §[3]): a width-4 poset with an element
  `x` incomparable to a 3-chain has near-flat slot law `≈ [0.23, 0.26, 0.26, 0.25]` — the
  block-cross shape, at a width the width-3 arc's Cauchy–Schwarz could not even *state*.
- **No step references width.** (A) uses only (H); (GID) is pure combinatorics; (★global) and
  (decay) never split `Inc(x)`. A proof of (decay) would settle **all** widths simultaneously. There
  is **no silent width cap**.

---

## 5. Numerical checks (this session)

Script `scripts/onethird_mga7c5_global_chaincount_probe.py` (reuses mg-b0a6 `Poset`/LE engine;
exact rationals; deterministic):

- **[1]** `(GID)` and `Σ_m K_m ≤ inv` on 200 000 random permutations (`n ≤ 12`): **0 violations
  each**. The reformulation is an exact identity.
- **[2]** `E`-form of `(GID)` on exact LE ensembles at **width 4** (3 posets) and **width 5** (2
  posets): `E[Σdisp²] = 2E[Σ_m K_m] + 2Σ_{k<l}E[M_{k,l}]` exactly; width-agnostic.
- **[3]** width-4 witness: `x` incomparable to a 3-chain, near-flat slot law — the block-cross
  residual object at width 4.

Reproduce: `python3.11 scripts/onethird_mga7c5_global_chaincount_probe.py`.

---

## 6. Status table

| item | statement | status |
|---|---|---|
| **(A) SPREAD** | `‖r‖² = Ω(n³)`, any frozen `δ<1/3`, **any width** | **PROVEN** (mg-dbd1 §1; reused verbatim) |
| **(GID)** | `Σ_x disp² = 2Σ_m K_m + 2Σ_{k<l}M_{k,l}` | **PROVEN** (exact, width-free, hypothesis-free) |
| **(★global)** | `(B) ⟺ Σ_{k<l}E[M_{k,l}] = O(E[inv_e])` | **PROVEN reduction** (iff; no width constant; removes the mg-2acf `w−1` crutch) |
| (decay) sufficient | `E[M_{k,l}] ≤ Cρ^{l−k}E[K_k] ⟹ (★global)` | **PROVEN conditional**; replaces refuted log-concavity |
| envelope | `M_{k,l} ≤ 2min_{[k,l]}K_m` | **PROVEN but too lossy** (factor `n` on flat profiles) |
| **residual** | width-free block-cross non-realizable under whole-poset `δ<1/3` | **OPEN — same wall as width 3, now width-free** (DUAL-RESIST) |
| (aux) `Λ=O(1)` | no `O(n)` gap in sorted expected ranks | open, separate (mg-dbd1 §3.4) |

---

## 7. Recommendation (pre-committed strategic surface; no tickets filed)

Per the mg-a7c5 stop-loss (asymptotic-AMBER = stop and surface) and pre-committed clause:

1. **The re-scope is delivered.** (A) is general; the width-3 `≤2`-chain Cauchy–Schwarz crutch is
   **removed** and replaced by the exact width-free global reduction `(★global)`. The certificate
   route for L1b now type-checks at the **any-width** minimal counterexample the `.tex` targets,
   reduced to **one** clean object `Σ_{k<l}E[M_{k,l}]`.
2. **It walls on the same realizability theorem as width 3.** Closing `(★global)` needs (decay), and
   per-pair freezing provably cannot force it (block-cross flat-tail); a single realized deep
   block-cross is fatal (no global cancellation). This is the **poset-LE realizability theorem**
   mg-9de3 RED-pivoted on — now confirmed **width-free and at least as hard at any width**.
3. **Strategic go/no-go (Daniel).** The certificate route's viability at general width hinges
   *entirely* on that one realizability theorem. Options unchanged from the mg-9de3 fork, but now
   the fork is stated at the correct (general) scope:
   - **(a) Invest in the realizability theorem** — prove no frozen (`δ<1/3`) poset admits an
     element block-crossing a `Θ(n)` incomparable chain (a genuinely new poset-linear-extension
     tail/anti-concentration theorem; log-concavity is dead, so a different tool is required).
   - **(b) Pivot** to `project_onethird_algebraic_program_vision` (note: that program is itself
     width-3 per the drift audit Q5, so it does **not** address the any-width concern).
   - **(c) A different L1 attack** (the `.tex`'s BK-transport porting Problem, §11), independent of
     the block-cross tail.

**Bottom line.** *Any-width (B) is now one width-free realizability theorem from closed — the exact
theorem the width-3 arc also reduced to. The re-scope removed the drift (the width-3 crutch is gone;
the reduction is an exact iff at any width), but did not, and per §2 cannot by elementary means,
close the residual. AMBER, with the residual pinned width-free and the strategic call surfaced.*

---

# 8. mg-0508 — attacking the single residual via a GLOBAL argument (successor to mg-a7c5)

**Work item:** mg-0508 (successor to mg-a7c5). Target: prove the width-free geometric far-tail
decay `E[M_{k,l}] ≤ Cρ^{l−k}E[K_k]` (`C, ρ` width-free, `0<ρ<1`) via a **global / joint** argument,
or refute it with an any-width counterexample. FORBID (honored): no per-pair freezing as the
decay mechanism (refuted, §2.3), no width bound load-bearing (sanity-checked at width > 3 below),
no `≤2`-chain Cauchy–Schwarz, no monotonicity (mg-b0a6).

## 8.0 Verdict: **AMBER — same family (tail-decay / realizability) as a7c5 ⟹ TRIP-WIRE FIRED.**

The residual is **crystallized** to its sharpest analytic form and the "pinned above `1/3`" evidence
is **reproduced and extended to width > 3** with a new global experiment — but no global/joint tool
delivers the decay, and no any-width counterexample is realizable. Because a7c5 was AMBER with a
residual in the **same family** (tail-decay / realizability), this is the **second consecutive**
such AMBER, so per the mg-0508 pre-committed trip-wire it is **surfaced to PM before any third
iteration** rather than iterated silently. **NOT PROVEN. NOT RED.**

## 8.1 The sharpest equivalent of (B) (even cleaner than (★global))

`disp_σ(x) = pos_σ(x) − x` **exactly** (labels by `e`). Since `Σ_x E|disp_x| = 2E[Σ_m K_m] ≍ E[inv]`,

> **(B)  ⟺  `Σ_x E[disp_x²] = O( Σ_x E|disp_x| )`**   — *"no heavy displacement tail."*

Diagonal identity: writing `disp_x = Σ_{b>_e x} J_{xb} − Σ_{a<_e x} J_{ax}` with the inversion
indicator `J_{ab}=1[b before a]` (`E[J_{ab}]=p_{ab}<1/3`),
```
Σ_x disp_x²  =  2·inv_e  +  2 Σ_{cherries P,Q sharing a vertex x} ε_P ε_Q J_P J_Q,
```
so the **diagonal is `2·inv` unconditionally** and **(B) ⟺ the total *signed cherry-correlation*
`= O(E[inv])`**. The dangerous terms are the **same-side cherries** (`b,b' >_e x`), which
**Shepp's XYZ inequality forces to be *positively* correlated** — i.e. the one available joint tool
pushes in the **wrong direction** for an upper bound. (FKG / Ahlswede–Daykin likewise only give the
`≥` direction here.)

## 8.2 The chain-nesting crystallization (the new content)

Take `x` incomparable to a chain `C: c_1 <_P ⋯ <_P c_p` (all `c_i` incomparable to `x`). Because
`c_i <_P c_{i+1}` forces `c_i` before `c_{i+1}` in **every** LE, the events `A_i := {c_i before x}`
are **nested**:
```
A_1 ⊇ A_2 ⊇ ⋯ ⊇ A_p ,     q_i := Pr[A_i] = Pr[c_i before x]  is DECREASING,  q_i < 1/3  (freezing).
```
Let `g = #{c_i before x} = max{i : A_i}` (by nesting). Then `Pr[g≥i]=q_i`, `E[g]=Σ q_i`,
`E[g²]=Σ(2i−1)q_i`, and:

- **`Pr[x AFTER the whole chain] = q_p = Pr[c_p before x]` — literally ONE frozen pair** (so `<1/3`,
  bounded, but **not** decaying in `p`); `Pr[x BEFORE the whole chain] = 1 − q_1 > 2/3`.
- **Single-element (B)-badness ratio** `= E[g²]/E[g] = Σ(2i−1)q_i / Σ q_i`.

> **The wall, crystallized.** `(decay)` for this element `⟺` `q_i` decays **geometrically**
> `⟺` the **conditional threshold-contraction** `ρ_i := Pr[c_{i+1} bef x | c_i bef x] = q_{i+1}/q_i`
> is `≤ ρ < 1` uniformly.
>
> - The **flat law** `q_i ≡ q < 1/3` (i.e. `ρ_i = 1`) satisfies **every** frozen pairwise marginal
>   yet gives `E[g²]/E[g] = Θ(p)`; with `p = Θ(n)` this is `R := E[Σdisp²]/E[inv] = Θ(n)` — **(B)
>   FALSE**. So **marginal freezing is provably insufficient**; decay must come from the **joint**
>   poset-LE structure.
> - `q_p < 1/3` does **not** save it: the threat is `p²·q_p` (deep), not `q_p`.
> - The natural closing tool — slot-law **log-concavity / real-rootedness** (Neggers–Stanley) — is
>   **false** (mg-2acf: 7 537 violations). No elementary joint tool forces `ρ_i ≤ ρ<1`.

This is the a7c5 residual reduced to its irreducible core: **"do the conditional deep-crossing
probabilities of an element over an incomparable chain contract geometrically in a frozen poset?"**
It confirms a7c5 §2.4 exactly — a **single** flat-long element is fatal (no global cancellation
survives it), so `(★global)` fails **iff** such an element is realizable.

## 8.3 New evidence — the FREEZING FRONTIER at width > 3 (`scripts/onethird_mg0508_freezing_frontier_probe.py`)

For a poset let `Bworst = max over incomparable pairs of balance` (the **least-frozen** pair; (H)
`⟺ Bworst < 1/3`) and `R = E[Σdisp²]/E[inv]`. The realizability question is whether a **deep tail**
(large `R`, or `Pr[x after an incomparable chain]` deep) can coexist with `Bworst < 1/3`.

- **[1] Global random search, width ≥ 4** (5 579 exact-LE ensembles, `n ≤ 8`): `min Bworst = 0.4010`
  — **no** sampled width-≥4 poset even reaches `Bworst < 0.40`. The `(Bworst, R)` **Pareto frontier
  is monotone**: `R≥4 ⟹ Bworst≥0.401`, `R≥5 ⟹ Bworst≥0.427`, `R≥6 ⟹ Bworst≥0.500`. **Pushing the
  (B) ratio up *forces* un-freezing.**
- **[2] Structured block-cross family** (element `x` incomparable to a length-`p` chain, ballast
  hill-climbed to bias `x` early while sustaining `Pr[x after chain] ≥ 0.10`): the **minimum
  achievable `Bworst` is pinned at `1/3` and GROWS with block length** —
  `p=2: 0.3333`, `p=3: 0.4000`, `p=4: 0.4000` — **never frozen** (`Bworst < 1/3` never achieved),
  and the pin moves **away** from `1/3` as the tail deepens. This reproduces the a7c5 / mg-9de3
  "pinned at ≥ 0.357" finding, now **at width > 3, under a global search, and monotone in `p`** —
  precisely the opposite of what a RED refutation would need.

Width guard satisfied: every observable is width-agnostic; the search is at width ≥ 4; nothing caps
the width. Reproduce: `python3.11 scripts/onethird_mg0508_freezing_frontier_probe.py`.

## 8.4 Why not PROVEN, why not RED

- **Not PROVEN.** Closing `(decay)` requires forcing `ρ_i ≤ ρ<1` (§8.2). The only joint tools
  (Shepp XYZ, FKG) give the **wrong-signed** inequality; slot-law log-concavity is **dead**; and no
  global cancellation can rescue a single realized flat-long element. A proof needs a genuinely new
  **poset-linear-extension anti-concentration theorem** — not an elementary global argument.
- **Not RED.** Refutation needs a **realized** frozen poset (`Bworst < 1/3`) carrying a flat-long
  element; every construction (directed and now global-search, width > 3) is **pinned strictly above
  `1/3`**, with the pin **growing** as the tail deepens. Evidence **leans (B)-TRUE**; a counterexample
  is out of empirical reach (and would itself be a `1/3`–`2/3` counterexample).

## 8.5 Recommendation — trip-wire fired (surface, do not iterate a third time)

Per the mg-0508 pre-committed trip-wire ("if this is the SECOND consecutive AMBER whose residual is
in the same family (tail-decay / realizability), surface to PM BEFORE any third iteration —
asymptotic-AMBER often precedes a PROVEN structural RED and should not be iterated silently"):

1. **This is that second consecutive same-family AMBER.** a7c5 named the residual (block-cross
   realizability); mg-0508 crystallized it to conditional threshold-contraction `ρ_i ≤ ρ<1` and
   added width->3 global evidence — **same family, no qualitative shape change** (asymptotic-AMBER).
   Per the stop-loss this is **STOP-and-surface**, not a third tightening pass.
2. **The strategic go/no-go is unchanged from a7c5 §7 and now sharper.** The certificate route for
   L1b at **any width** hinges **entirely** on one poset-LE anti-concentration theorem: *no frozen
   (`δ<1/3`) poset has an element whose conditional deep-crossing probabilities over an incomparable
   chain fail to contract geometrically* (equivalently, no realizable flat-long block-cross). This
   is a **Daniel/PM-level** call:
   - **(a)** Invest in that anti-concentration theorem directly (new tool required; log-concavity is
     dead). It would close (B) at **all widths** simultaneously.
   - **(b)** Pivot to `project_onethird_algebraic_program_vision` (note: width-3 per drift audit Q5;
     does not address the any-width concern).
   - **(c)** A different L1 attack — the `.tex` BK-transport porting Problem (§11), independent of the
     block-cross tail.
3. **The asymptotic-AMBER warning is live:** two same-family AMBERs with a dead natural tool and a
   wrong-signed joint tool is the classic precursor to a **structural RED** on the *route* (the
   certificate cannot be closed by elementary means) even though the *statement* (B) leans TRUE.
   The decision on whether the anti-concentration theorem is worth a dedicated arc should be made
   **before** any third pass on the same object.

**Bottom line (mg-0508).** *The residual is now irreducibly sharp — a single conditional-contraction
`ρ_i ≤ ρ<1`, provably beyond marginal freezing, with the natural tool dead and the joint tools
wrong-signed — and it is pinned above `1/3` under a global, width->3 search that only tightens with
depth. Second consecutive tail-decay/realizability AMBER: trip-wire fired, surfaced to PM. Neither an
elementary global proof nor an any-width counterexample exists in reach.*
