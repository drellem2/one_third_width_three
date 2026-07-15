# OneThird L1b — a self-contained proposed CORE LEMMA (for Daniel to attempt)

**Purpose.** This document states **one** rigorously-defined, **self-contained** lemma whose
proof closes the last open step (**(B) LOCALITY**) of the spectral / near-ordinal-sum route to the
1/3–2/3 conjecture, at **any width**. Every object is defined inline: a competent mathematician who
has never seen the surrounding arc should be able to read only this file and start attempting a
proof.

**Scope discipline.** This is an **extraction**, not a research note. The lemma is stated at the
sharpest honest form the arc has crystallized; it is **not** weakened to be easier nor strengthened.
No proof is attempted here. Where the source leaves a genuine modelling choice open, it is flagged
explicitly in §6 rather than silently resolved.

**Provenance (for the curious; not needed to attempt the lemma).** The statement is the residual of
`docs/OneThird-L1b-general-Bwall-state.md` (§8.2, the *conditional threshold-contraction*
crystallization) together with the exact width-free identity (GID) of that document's §1.2. The
any-width baseline is `spectral_near_ordinal_sum_program.tex`. Nothing below imposes a width bound.

---

## 1. Preamble — all definitions inlined

Throughout, $P$ is a **finite poset** on the ground set $[n]=\{1,\dots,n\}$, with strict order
$<_P$. Two elements are **incomparable**, written $x \parallel y$, if neither $x<_P y$ nor $y<_P x$.
A **linear extension** of $P$ is a total order refining $<_P$; we identify it with the bijection
$\sigma:\{0,\dots,n-1\}\to[n]$ sending each **position** to the element occupying it, so that
$a<_P b \Rightarrow \operatorname{pos}_\sigma(a)<\operatorname{pos}_\sigma(b)$. Positions are
**0-indexed**: $\operatorname{pos}_\sigma(x)\in\{0,\dots,n-1\}$. Write $\mathcal L(P)$ for the set
of linear extensions and let $\sigma$ be drawn **uniformly at random** from $\mathcal L(P)$; all
expectations $\mathbb E[\cdot]$ and probabilities $\Pr[\cdot]$ are over this uniform law.

For distinct incomparable $x,y$, put $p_{xy}=\Pr[\operatorname{pos}_\sigma(x)<\operatorname{pos}_\sigma(y)]$
(the probability $x$ precedes $y$). The **balance constant** is
$$\delta(P)=\max_{x\parallel y}\ \min\{p_{xy},\,1-p_{xy}\}.$$

### 1.1 The frozen (minimal-counterexample) hypothesis (H)

A **counterexample** to the 1/3–2/3 conjecture is a non-chain poset with $\delta(P)<\tfrac13$.
The surrounding minimal-counterexample theory supplies a **distinguished order**: a total order $e$
on $[n]$ such that for every incomparable pair the strict-majority ($>2/3$) orientation agrees with
$e$. We assume this and **relabel elements by their $e$-rank**, so that
$$e=1\,2\,\cdots\,n,\qquad\text{and for every incomparable }i<j:\quad \Pr[j\prec_\sigma i]<\tfrac13 .$$
Here $j\prec_\sigma i$ means $\operatorname{pos}_\sigma(j)<\operatorname{pos}_\sigma(i)$, i.e. the
$e$-larger element $j$ lands before the $e$-smaller element $i$ (an **$e$-inversion**). Comparable
pairs never $e$-invert (since $e$ refines $<_P$). This is the standing hypothesis:

> **(H) [frozen].** $P$ is labelled by its distinguished order $e=1\cdots n$, and **every**
> incomparable pair $i<j$ has $\Pr[j\prec_\sigma i]<\tfrac13$. Equivalently $\delta(P)<\tfrac13$
> with the majority orientation acyclic and realized by $e$. **No width hypothesis is imposed.**

### 1.2 Displacement, inversions, cut leakage, block-crossings

Fix a linear extension $\sigma$. All objects below are labelled by $e$-rank (so element $x$ has
$e$-rank $x$).

- **Displacement.** $\operatorname{disp}_\sigma(x)=\operatorname{pos}_\sigma(x)-x$, the signed
  footrule displacement of $x$ against $e$. (With 0-indexing, $e$-rank $x$ sits at position $x$, so
  $\operatorname{disp}_\sigma(x)=0$ for all $x$ iff $\sigma=e$.)

- **$e$-inversion count.** $\operatorname{inv}_e(\sigma)=\#\{\text{incomparable pairs } i<j :
  j\prec_\sigma i\}$, the Kendall distance of $\sigma$ from $e$. (Only incomparable pairs can
  contribute.) Its uniform mean is $\mathbb E[\operatorname{inv}_e]$.

- **Cut and leakage.** For $1\le m\le n-1$ the **cut** $m$ separates the $e$-prefix
  $\{1,\dots,m\}$ from the $e$-suffix $\{m+1,\dots,n\}$. The **leakage across cut $m$** is
  $$K_m(\sigma)=\#\{x:\ x\le m,\ \operatorname{pos}_\sigma(x)\ge m\}
  \quad(\text{$e$-prefix elements pushed into the suffix}).$$
  By bijectivity the same number of suffix elements are pulled into the prefix, so the total number
  of elements crossing cut $m$ (in either direction) is $2K_m$.

- **Crossing a cut.** Element $x$ **crosses cut $m$** iff exactly one of its $e$-rank $x$ and its
  position $\operatorname{pos}_\sigma(x)$ is $\le m-1$; equivalently
  $\min(x,\operatorname{pos}_\sigma(x))<m\le\max(x,\operatorname{pos}_\sigma(x))$. The number of cuts
  $x$ crosses equals $|\operatorname{disp}_\sigma(x)|$.

- **Block-crossing.** For $1\le k<l\le n-1$, the **block-cross count**
  $$M_{k,l}(\sigma)=\#\{x:\ x\text{ crosses BOTH cut }k\text{ and cut }l\}
  =\#\{x:\ \min(x,\operatorname{pos}_\sigma(x))<k\ \text{and}\ l\le\max(x,\operatorname{pos}_\sigma(x))\},$$
  the number of elements whose displacement interval spans the **entire** block $(k,l]$. (Any such
  $x$ also crosses every intermediate cut $m\in[k,l]$.)

### 1.3 The chain block-cross setup and the contraction ratio $\rho_i$

Let $x\in[n]$ and let $C:\ c_1<_P c_2<_P\cdots<_P c_p$ be a **chain** in $P$ (so $p=|C|$) with
every $c_s\parallel x$ (an **incomparable chain** of $x$). Because $c_s<_P c_{s+1}$ forces
$\operatorname{pos}_\sigma(c_s)<\operatorname{pos}_\sigma(c_{s+1})$ in **every** $\sigma$, the events
$$A_s:=\{c_s\prec_\sigma x\}\quad\text{are NESTED:}\quad A_1\supseteq A_2\supseteq\cdots\supseteq A_p,$$
and $q_s:=\Pr[A_s]=\Pr[c_s\prec_\sigma x]$ is **non-increasing** in $s$. Writing
$g:=\#\{s:c_s\prec_\sigma x\}=\max\{s:A_s\}$ (well-defined by nesting), one has $\Pr[g\ge s]=q_s$,
$\ \mathbb E[g]=\sum_s q_s,\ \mathbb E[g^2]=\sum_s(2s-1)q_s$. Define the **conditional
threshold-contraction ratio**
$$\boxed{\ \rho_s:=\Pr[c_{s+1}\prec_\sigma x\mid c_s\prec_\sigma x]=\frac{q_{s+1}}{q_s}\in[0,1]\ }
\qquad(1\le s\le p-1),$$
the conditional probability that, **given** $x$ has already fallen behind $c_s$, it also falls
behind the next chain element $c_{s+1}$. (When $x$ is $e$-below all of $C$, hypothesis (H) forces
$q_s<\tfrac13$ for every $s$, but says **nothing** directly about the ratios $\rho_s$.)

**Symbol table (every symbol the lemma uses).**

| symbol | meaning | defined |
|---|---|---|
| $\mathcal L(P),\ \sigma$ | linear extensions; uniform random one | §1 |
| $\operatorname{pos}_\sigma(x)$ | 0-indexed position of $x$ | §1 |
| $\delta(P)$; (H) | balance constant; frozen hypothesis | §1, §1.1 |
| $e,\ i\prec_\sigma j$ | distinguished order $=12\cdots n$; $\operatorname{pos}(i)<\operatorname{pos}(j)$ | §1.1 |
| $\operatorname{disp}_\sigma(x)$ | $\operatorname{pos}_\sigma(x)-x$ | §1.2 |
| $\operatorname{inv}_e(\sigma)$ | # $e$-inversions (incomparable pairs only) | §1.2 |
| $K_m(\sigma)$ | leakage across cut $m$ | §1.2 |
| $M_{k,l}(\sigma)$ | # elements block-crossing $(k,l]$ | §1.2 |
| $q_s,\ \rho_s$ | $\Pr[c_s\prec x]$; contraction $q_{s+1}/q_s$ | §1.3 |
| $g$ | # of $C$ ahead of $x$ | §1.3 |

**Two exact background identities** (pure combinatorics, used freely; proofs in the source, not
needed to attempt the lemma):

- **(GID)** — width-free, hypothesis-free, holds for every $\sigma$:
  $$\sum_x \operatorname{disp}_\sigma(x)^2 \;=\; 2\sum_{m} K_m(\sigma)\;+\;2\sum_{k<l} M_{k,l}(\sigma).$$
  (Because $|\operatorname{disp}(x)|=$ # cuts $x$ crosses, and
  $|\operatorname{disp}|^2=|\operatorname{disp}|+2\binom{|\operatorname{disp}|}{2}$ counts crossed
  cuts with the pair-multiplicity that reindexes to $\sum_{k<l}M_{k,l}$.)
- **(DG)** — Diaconis–Graham, pointwise: $\sum_m K_m(\sigma)\le \operatorname{inv}_e(\sigma)$ and
  $\operatorname{inv}_e(\sigma)\le 2\sum_m K_m(\sigma)$; hence
  $\mathbb E[\operatorname{inv}_e]\asymp \mathbb E[\sum_m K_m]$.

---

## 2. The lemma

> ### CORE LEMMA (frozen block-cross contraction — any width). 
> There exist **absolute** constants $C<\infty$ and $\rho\in(0,1)$ — independent of $P$, of $n$, and
> of the width of $P$ — such that the following holds. For **every** finite poset $P$ satisfying the
> frozen hypothesis **(H)** of §1.1 (labelled by $e=12\cdots n$, every incomparable pair
> $\Pr[j\prec_\sigma i]<\tfrac13$), and for **all** cuts $1\le k<l\le n-1$,
> $$\boxed{\ \mathbb E\big[M_{k,l}\big]\ \le\ C\,\rho^{\,l-k}\,\mathbb E\big[K_k\big].\ }\tag{decay}$$

In words: **under freezing, the expected number of elements that block-cross an entire span
$(k,l]$ decays geometrically in the span length $l-k$, relative to the leakage across the near cut
$k$.** This is a statement about a single frozen poset with **no reference to width** and no free
parameters other than the two absolute constants.

**Why this form is the primary target.** $\mathbb E[M_{k,l}]/\mathbb E[K_k]$ is a *conditional
deep-crossing probability*: given that some element crosses the near cut $k$, how likely is a
block-crosser to reach past the far cut $l$. (decay) asserts this contracts geometrically. It is the
cleanest self-contained object the arc reduces to, and it **implies (B)** directly (see §3).

### 2.1 Equivalent / adjacent forms (one line each; pointers, not re-derivations)

All three are the **same residual** viewed differently. Prove any sufficient form and (B) closes.

1. **Exact global iff (what (decay) feeds).** Via (GID)+(DG),
   $$\textbf{(B)}\ \Longleftrightarrow\ \sum_{k<l}\mathbb E[M_{k,l}]=O\big(\mathbb E[\operatorname{inv}_e]\big).\tag{$\star$}$$
   (decay) $\Rightarrow$ ($\star$): summing $\sum_{l>k}C\rho^{\,l-k}\mathbb E[K_k]\le
   \frac{C}{1-\rho}\mathbb E[K_k]$ then $\sum_k$ gives $O(\mathbb E[\sum_m K_m])=O(\mathbb E[\operatorname{inv}_e])$.
   See `OneThird-L1b-general-Bwall-state.md` §1.3, §2.2.
2. **Per-element conditional contraction (the sharpest micro-form).** For $x$ incomparable to a
   chain $C$ with $x$ $e$-below $C$, (decay) for that element $\Longleftrightarrow$ the slot masses
   $q_s=\Pr[c_s\prec_\sigma x]$ decay geometrically $\Longleftrightarrow$ the contraction ratios
   satisfy $\rho_s\le\rho<1$ uniformly (§1.3). The single-element badness ratio is
   $\mathbb E[g^2]/\mathbb E[g]=\sum_s(2s-1)q_s/\sum_s q_s$; it is $\Theta(p)$ iff the $q_s$ are flat
   ($\rho_s\equiv1$). See same doc §8.2.
3. **Refutation-side (necessity) form.** ($\star$) **fails** iff a single element realizes a
   **flat-long block-cross**: an $x$ and a length-$p=\Theta(n)$ incomparable chain $C$ with slot law
   $q_s$ carrying $\Theta(1)$ mass at the far end $s=p$ (so $x$ trails the whole block a constant
   fraction of the time). A single such element already forces
   $\sum_{k<l}M_{k,l}=\Theta(n^2)$ against $\operatorname{inv}_e=\Theta(n)$, and **no cancellation
   over other elements can undo it**. So
   $$\textbf{(B) at any width}\ \Longleftrightarrow\ \text{NO frozen poset admits a flat-long block-cross}\ \Longleftrightarrow\ \rho_s\le\rho<1\ \text{always}.$$
   See same doc §2.4, §8.2.

**Logical status to keep straight.** (decay) and forms 1–2 are **sufficient** for (B); form 3 is the
**necessity** direction. Because a single realized flat-long element is fatal, the sufficient and
necessary conditions **coincide up to the geometric-rate packaging**, which is why the arc treats
this as *the* residual rather than merely *a* sufficient condition. Daniel's cleanest target is
(decay) (equivalently: prove $\rho_s\le\rho<1$ uniformly over all elements and incomparable chains
of a frozen poset).

---

## 3. Why this closes L1b (B)

The spectral certificate (proven parts, reused verbatim — see `OneThird-L1b-Spread-Locality.md`)
reduces the 1/3–2/3 conjecture, for any frozen counterexample, to two factors of the centred
expected-rank test vector $r$ with $r_x=\mathbb E[\operatorname{pos}_\sigma(x)]-\tfrac{n-1}{2}$:
$$1-\lambda_{\mathrm{std}}(P)\ \le\ \frac{\mathrm{energy}(r)}{\|r\|^2}\ \le\ \tfrac12\Lambda^2\,
\frac{\mathbb E[\sum_x\operatorname{disp}_\sigma(x)^2]}{\|r\|^2},$$
where the numerator is controlled by **(B) LOCALITY** $\mathbb E[\sum_x\operatorname{disp}^2]=
O(\mathbb E[\operatorname{inv}_e])$ and the denominator by **(A) SPREAD** $\|r\|^2=\Omega(n^3)$.
With both, $1-\lambda_{\mathrm{std}}=O(\mathbb E[\operatorname{inv}_e]/n^3)=O(1/n)\to0$, i.e. bad
mixing forces $\lambda_{\mathrm{std}}\to1$ — the porting lemma L1 the program needs, at any width.

**The exact iff this lemma feeds.** By (GID), $\mathbb E[\sum_x\operatorname{disp}^2]=
2\mathbb E[\sum_m K_m]+2\sum_{k<l}\mathbb E[M_{k,l}]$, and by (DG) the first term is
$\Theta(\mathbb E[\operatorname{inv}_e])$ unconditionally. Hence **(B) holds iff
$\sum_{k<l}\mathbb E[M_{k,l}]=O(\mathbb E[\operatorname{inv}_e])$** — precisely ($\star$) — and the
Core Lemma (decay) $\Rightarrow$ ($\star$) $\Rightarrow$ (B). Per the source, the route hinges
**entirely** on this: (decay) is not merely sufficient but is the last load-bearing gap; a realized
flat-long block-cross would break (B) outright.

**Auxiliary facts the lemma MAY assume already proven** (do **not** re-prove these):

- **(GID)** $\sum_x\operatorname{disp}^2=2\sum_m K_m+2\sum_{k<l}M_{k,l}$ — exact permutation identity.
- **(DG)** Diaconis–Graham $\sum_m K_m\le\operatorname{inv}_e\le2\sum_m K_m$ (so
  $\mathbb E[\operatorname{inv}_e]\asymp\mathbb E[\sum_m K_m]$).
- **(A) SPREAD** $\|r\|^2=\Omega(n^3)$ under (H), any width (proven; band bound, uses only (H)).
- The existence of the distinguished order $e$ (minimal-counterexample theory).

**What must be proven:** the Core Lemma (decay) itself — equivalently the uniform contraction
$\rho_s\le\rho<1$, equivalently ($\star$). Nothing else.

**Separable smaller gap (not part of this lemma).** The certificate also needs a Lipschitz constant
$\Lambda=O(1)$ (no $\Theta(n)$ gap in the sorted expected-rank spectrum); this is a distinct, likely
easier smoothness fact, not what Daniel is being asked to prove here.

---

## 4. A small worked instantiation (width 4)

To sanity-check that the definitions mean what one expects, here is a concrete poset of **width 4**
(> 3, honoring any-width) with every object computed exactly by full linear-extension enumeration.

**The poset $P_0$.** Ground set $[6]=\{1,\dots,6\}$, sole relations $2<_P 3<_P 4$ (a 3-chain);
elements $1,5,6$ carry no relations. Labelled by $e$-rank $0,\dots,5$ (0-indexed), take:
$$x:=\text{rank }0,\qquad C:\ c_1<c_2<c_3=(\text{ranks }1,2,3),\qquad \text{free: ranks }4,5.$$
So $x\parallel C$ (element of rank 0 is incomparable to the whole chain), and $\{$rank 0, rank 1,
rank 4, rank 5$\}$ is a 4-antichain $\Rightarrow$ **width $=4$**. There are $|\mathcal L(P_0)|=120$
linear extensions.

**Global objects (exact).**

| quantity | value |
|---|---|
| $\mathbb E[\sum_x\operatorname{disp}^2]$ | $28$ |
| $\mathbb E[\operatorname{inv}_e]$ | $6$ |
| $\mathbb E[\sum_m K_m]$ | $59/12\approx4.917$ |
| $\sum_{k<l}\mathbb E[M_{k,l}]$ | $109/12\approx9.083$ |
| ratio $\mathbb E[\sum\operatorname{disp}^2]/\mathbb E[\operatorname{inv}_e]$ | $28/6\approx4.667$ |

**(GID) checks exactly:** $2\cdot\tfrac{59}{12}+2\cdot\tfrac{109}{12}=\tfrac{336}{12}=28
=\mathbb E[\sum\operatorname{disp}^2]$. **(DG) holds:** $\tfrac{59}{12}\le 6$.

**Per-cut leakage** $\mathbb E[K_m]$ for $m=1,\dots,5$:
$\;0.833,\ 0.867,\ 1.050,\ 1.333,\ 0.833.$

**Block-cross table** $\mathbb E[M_{k,l}]$:

| | $l=2$ | $l=3$ | $l=4$ | $l=5$ |
|---|---|---|---|---|
| $k=1$ | $1.000$ | $0.833$ | $0.667$ | $0.333$ |
| $k=2$ | | $1.217$ | $1.000$ | $0.500$ |
| $k=3$ | | | $1.533$ | $0.667$ |
| $k=4$ | | | | $1.333$ |

Reading off the near cut $k=1$: $\mathbb E[M_{1,l}]=1.000,\,0.833,\,0.667,\,0.333$ for
$l=2,3,4,5$ — monotone decreasing in the span, the qualitative shape (decay) asserts (here at
tiny $n$, not a rate estimate).

**The block-cross micro-object** (element $x=$ rank 0 vs its incomparable chain $C=(c_1,c_2,c_3)=$
ranks $1,2,3$). Slot masses $q_s=\Pr[c_s\prec_\sigma x]$ and contraction ratios:
$$q_1=\tfrac34=0.750,\quad q_2=\tfrac12=0.500,\quad q_3=\tfrac14=0.250;\qquad
\rho_1=\tfrac{q_2}{q_1}=\tfrac23,\quad \rho_2=\tfrac{q_3}{q_2}=\tfrac12.$$
Both $\rho_s<1$: this element **contracts** (the "good" case). Also $\mathbb E[g]=\tfrac32$,
$\mathbb E[g^2]=\tfrac72$, single-element ratio $\mathbb E[g^2]/\mathbb E[g]=\tfrac{7}{3}\approx2.33$
(bounded, as it must be when $\rho_s$ is bounded below $1$).

> **Honest caveat on this instantiation (important).** $P_0$ is **not** frozen: $\delta(P_0)=\tfrac12$,
> and indeed $q_1=\tfrac34>\tfrac23$, so the pair $\{x,c_1\}$ violates (H). This is **unavoidable**:
> a frozen poset ($\delta<\tfrac13$) would *be* a counterexample to the 1/3–2/3 conjecture, so no
> genuinely-frozen example can be exhibited (the empirical record finds none — $0$ in $20{,}000$
> dense width-$\ge3$ trials, and every directed construction is pinned at $\delta\ge0.357$, above
> $\tfrac13$). $P_0$ is included **only** to make the definitions ($K_m$, $M_{k,l}$, $q_s$,
> $\rho_s$, GID, DG) concrete and checkable; it is an *illustration of the objects*, not an instance
> of the hypothesis. The Core Lemma's whole content is exactly what happens to these objects in the
> (empirically unreachable) frozen regime.

Reproduce: `python3 scripts/onethird_mg69be_corelemma_instantiation.py` (full LE enumeration, exact
rationals; verifies GID, DG, the $M_{k,l}$ table, and the $q_s/\rho_s$ slot law printed above).

---

## 5. Appendix — tools known DEAD (do not re-walk)

Recorded so the attempt does not re-derive known dead ends. One line each, with a pointer.

- **Per-pair / marginal freezing is insufficient (REFUTED).** Bounding each single-pair inversion by
  $<\tfrac13$ does **not** force (decay): the flat slot law $q_s\equiv q<\tfrac13$ (i.e.
  $\rho_s\equiv1$) satisfies **every** frozen pairwise constraint yet gives $\mathbb E[g^2]/\mathbb E[g]=\Theta(p)$.
  Decay must come from the **joint** LE structure, not the marginals. (`…general-Bwall-state.md`
  §2.3, §8.2.)
- **Slot-law log-concavity / real-rootedness is FALSE (DEAD).** The natural closing tool — that the
  linear-extension slot polynomial $e(P_m)$ is log-concave (⟹ geometric tail) — is numerically
  false: $7{,}537$ violations; Neggers–Stanley non-real-rootedness. (`…L1b-Bwall-state.md` §4 /
  `…general-Bwall-state.md` §8.2.)
- **FKG / Ahlswede–Daykin give the WRONG direction (DEAD for an upper bound).** The same-side cherry
  correlations that (B) needs bounded **above** are forced $\ge0$ (positively correlated) by these
  inequalities. (`…general-Bwall-state.md` §8.1.)
- **Shepp's XYZ inequality is WRONG-SIGNED (DEAD for an upper bound).** XYZ forces the dangerous
  same-side terms ($b,b'>_e x$) to be **positively** correlated — pushing the ratio up, the opposite
  of what an upper bound needs. (`…general-Bwall-state.md` §8.1.)
- **Leakage-envelope $M_{k,l}\le 2\min_{[k,l]}K_m$ is too lossy (TRUE but useless).** Sharp for spike
  leakage profiles but loses a factor $n$ on flat profiles; the true content is *spanning*, not
  per-cut leakage. (`…general-Bwall-state.md` §2.1.)
- **No global cancellation rescue.** One might hope block-crossers "compete for space" and cancel in
  the global sum; they do not — a single element block-crossing a $\Theta(n)$ interval contributes
  $\Theta(n^2)$ while costing only $\Theta(n)$ inversions. (`…general-Bwall-state.md` §2.4.)

**Net.** Proving (decay) requires a genuinely new **poset-linear-extension anti-concentration
theorem** forcing $\rho_s\le\rho<1$ under whole-poset freezing; log-concavity is dead and the joint
correlation inequalities are wrong-signed, so a different tool is required.

---

## 6. Open modelling choices (flagged, not silently resolved)

Points where the source leaves a genuine choice; Daniel should know exactly what he is being asked.

1. **"Absolute" vs "$P$-uniform" constants.** The lemma is stated with $C,\rho$ **absolute**
   (independent of $P$ and $n$). The source's sufficient-condition derivation ((decay) $\Rightarrow$
   ($\star$)) only needs $C,\rho$ uniform over the cuts of a **single** $P$, with $\rho$ bounded away
   from $1$ **uniformly in $n$** across the frozen family. These coincide for closing (B); the
   absolute form is the clean target, but a proof giving $\rho=\rho(P)<1$ with
   $\sup_{P\text{ frozen}}\rho(P)<1$ is equally sufficient. Either reading is acceptable.

2. **Which cut plays the normalizer.** (decay) normalizes $\mathbb E[M_{k,l}]$ by the **near**-cut
   leakage $\mathbb E[K_k]$. The source states it this way; normalizing by $\mathbb E[K_l]$ (far cut)
   or by $\min_{[k,l]}\mathbb E[K_m]$ are non-equivalent variants. The near-cut form is the one that
   telescopes to ($\star$); use it.

3. **Global (decay) vs per-element contraction.** The primary statement (§2, form 1) is global over
   cut-pairs; the micro-form (§2.1 form 2) is per (element, incomparable chain). They are equivalent
   as closers of (B) because a single flat-long element is fatal, but a proof could target either.
   The per-element contraction $\rho_s\le\rho<1$ is the most self-contained micro-target; the global
   $\mathbb E[M_{k,l}]$ decay is the most directly-plugged-in. Both are stated; pick the handle that
   suits the tool.

4. **Chain choice in the micro-form.** In §1.3 the incomparable chain $C$ of $x$ is *any* chain in
   $\operatorname{Inc}(x)$; the refutation-side threat (§2.1 form 3) is a $p=\Theta(n)$ chain. The
   lemma must hold for **all** such $x$ and $C$; the hard case is long chains, but the statement
   quantifies over all.

---

*Extraction only — no proof attempted, statement neither weakened nor strengthened. Self-contained:
every symbol used in §2 is defined in §1. Any-width: no width bound appears in the hypothesis or in
any object; the worked instantiation is width 4.*
