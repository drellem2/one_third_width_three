# Compat-Geom — F18: (UCC.2) — `δ_n` injective for all `n`, via the null-homotopy of `ι_n` (mg-d039)

**Branch:** `polecat-cat-mg-d039` (new).
**Parent:** mg-4d3a (F17, GREEN-equivariant-uniform) §7.3 (the (UCC.2) handle, `ι_n^* = 0` form) + §8.3 (the recommended F18 target — attack `ι_n` directly).
**Chain:** mg-b352 (F11) → mg-ecf6 (F13) → mg-3839 (F14) → mg-8355 (F15) → mg-f893 (F16) → mg-4d3a (F17) → **mg-d039 (F18)**.
**Type:** Structural argument (order-complex topology / the order-homotopy lemma), with a light verification harness re-confirming the construction at `n = 3, 4, 5`. LaTeX-style Markdown; **no new axioms; no Lean changes.** Multi-session-able; cumulative state ledger in `docs/state-F18.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: GREEN-ucc2-proven.** The order-ideal inclusion `ι_n : Δ_n ↪ Δ_{n+1}` is **null-homotopic for every `n ≥ 3`**, by an explicit `S_n`-equivariant poset zig-zag. The construction invokes **no hypothesis at all** — not `Hyp(m)` for any `m`, not `(UCC)`, not the F17 reduction — so it is *unconditional*, and a fortiori it does not assume `Hyp(n+1)` (the circularity guard is discharged vacuously). Consequently `ι_n^* = 0` on `H̃^\ast(Δ_{n+1}) → H̃^\ast(Δ_n)` in every degree; by exactness of the cofiber long exact sequence, `ker(δ_n) = im(ι_n^*) = 0`, so

$$\boxed{\ \delta_n : \widetilde H^{n-2}(\Delta_n) \longrightarrow \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n)\ \text{ is injective, for every } n \ge 3.\ }$$

This is **(UCC.2)** for all `n`. With F17 establishing **(UCC.1) ⟺ Hyp(n)**, the master hypothesis **(UCC) is now COMPLETE**, and the F10 cohomological core (`Hyp(n)` for all `n`; H-Cox + sgn at general `n`; existence/uniqueness of `ω_bal^{(n)}`; the non-vanishing pairing) is **UNCONDITIONAL**.

**Deliverables:**
- `docs/compatibility-geometry-F18-ucc2-delta-injective.md` (this doc).
- `docs/state-F18.md` (cumulative state ledger).
- `scripts/compat_geom_F18_ucc2_delta_injective.py` — verification harness: `43 677` checks at `n = 3, 4, 5`, all pass, ≈ 2 s. Confirms `κ_n` well-defined and `S_n`-equivariant, the zig-zag comparabilities, the prism poset maps order-preserving, and — the load-bearing check — the explicit chain null-homotopy `D = P' − P` satisfying `∂D + D∂ = (ι_n)_\# − \mathrm{const}_\#` on every simplex of `Δ_n` (`n = 3, 4`, exact integer arithmetic). Plus a homology anchor: reduced Betti of `Δ_3, Δ_4` `= Hyp(3), Hyp(4)`.

---

## §0. Executive summary

### 0.1 Where F18 stands in the program

F10 reduced the general-`n` width-3 Kahn–Saks 1/3-2/3 theorem, gap-free, to the master hypothesis **(UCC) = (UCC.1) + (UCC.2)** (F10 §6.3). After F17:

- **(UCC.1)** — concentration + representation type of the cofiber `H̃^{n-1}(Δ_{n+1}/Δ_n)` — is **PROVEN for all `n`**: F17's n-uniform `S_n`-equivariant cofiber Morse reduction gives `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` as `S_n`-representations, unconditionally, so **(UCC.1) at level `n` ⟺ Hyp(n)** — discharged by the F10 induction itself.
- **(UCC.2)** — `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` injective — was, after F17, **the SOLE remaining conditional input** of the F10 cohomological core. Proven at `n = 3` (mg-59f3); open for general `n`.

**F18 closes (UCC.2).** F17 §8.3 made the recommendation precise: F17 rendered the *cofiber side* completely transparent, so (UCC.2) "can now be attacked as a question purely about the absolute tower `(Δ_n)_n` and the inclusion `ι_n`." F18 does exactly that — and the answer is clean: `ι_n` is null-homotopic.

### 0.2 What F18 proves

The cofiber long exact sequence of the pair `(Δ_{n+1}, Δ_n)` reads, in reduced cohomology,

$$\cdots \to \widetilde H^{n-2}(\Delta_{n+1}) \xrightarrow{\ \iota_n^*\ } \widetilde H^{n-2}(\Delta_n) \xrightarrow{\ \delta_n\ } \widetilde H^{n-1}(\Delta_{n+1}/\Delta_n) \to \cdots$$

Exactness at `H̃^{n-2}(Δ_n)` gives `ker(δ_n) = im(ι_n^*)`, so **(UCC.2)(n) ⟺ `ι_n^* = 0` on `H̃^{n-2}`** (F17 §7.3). F18 proves the strictly stronger, degree-uniform statement:

> **Theorem (F18, the null-homotopy theorem).** *For every `n ≥ 3`, the order-ideal inclusion `ι_n : Δ_n ↪ Δ_{n+1}` is null-homotopic. The null-homotopy is `S_n`-equivariant and is given by an explicit poset zig-zag. The construction is unconditional — it uses no `Hyp(m)`, no `(UCC)`, and no F17 result.*

The mechanism in one line: let `ω_n` be the partial order on `[n+1]` in which the new element `n` lies **below all of `[n]`** (a single vertex of `Δ_{n+1}`). The rule `κ_n(x) := x ∪ ω_n` ("cone `n` below everything") is an `S_n`-equivariant order-preserving map `PPF_n → PPF_{n+1}` with, pointwise,

$$\iota_n(x)\ \le\ \kappa_n(x)\ \ge\ \omega_n .$$

The order-homotopy lemma turns this zig-zag of comparable poset maps into `|ι_n| ≃ |κ_n| ≃ \mathrm{const}_{ω_n}`. Hence `ι_n` is null-homotopic, so `ι_n^*` (and `ι_{n,*}`) vanish in **every** degree, so `δ_n` is injective in every degree — in particular **(UCC.2)**.

### 0.3 What this means for the program

| | status after F18 |
|---|---|
| **(UCC.2)** (`δ_n` injective for general `n`) | **PROVEN for all `n ≥ 3`, unconditionally** (Thm. 4.1). No longer a conditional input. |
| **(UCC) as a whole** | **COMPLETE** — (UCC.1) ⟺ Hyp(n) (F17), (UCC.2) unconditional (F18). |
| F10 cohomological core (`Hyp(n)` all `n`; H-Cox + sgn at general `n`; `ω_bal^{(n)}` exists/unique; non-vanishing pairing) | **UNCONDITIONAL** — the induction `Hyp(n) ⇒ Hyp(n+1)` now closes with no free-standing hypothesis (§5). |
| The general-`n` width-3 1/3-2/3 theorem | The **cohomological core** (F10 Thm. parts (i)–(ii)) is **unconditional**. The **numerical width-3 conclusion** (part (iii)) additionally rests on **(ICOP-step)** and the **width-3 bridge** (F10 §7.3–§7.4) — both verified `n ≤ 6`, both reduced to clean uniform sub-statements, neither part of (UCC) and neither touched by F18. |
| Route (ii) | Remains **CLOSED-negative** (F16). |
| Route (iii) / mg-b345 | Remains **PARKED** — F18's mandate keeps it parked; its escalation trigger is not met (the internal route delivered both (UCC.1) *and* (UCC.2)). |
| Lean trust surface | **Untouched** — no new axioms, no Lean changes (the F10 4-axiom in-tree artifact is a separate track). |

### 0.4 The verdict in one line

> **`ι_n` is null-homotopic** — the inclusion of `Δ_n` into `Δ_{n+1}` factors, up to homotopy, through a point, by the explicit `S_n`-equivariant poset zig-zag `ι_n ≤ κ_n ≥ \mathrm{const}_{ω_n}`. No hypothesis is used: the argument is unconditional, hence non-circular by construction. Therefore `ι_n^* = 0`, `δ_n` is injective, **(UCC.2) holds for all `n`**, **(UCC) is complete**, and the **F10 cohomological core is unconditional**.

---

## §1. Setting and the object (recap)

**Notation** (F1-refined / F2 / F5 / F14 §0.2 / F17 §1). `[n] = {0,…,n−1}`. A *partial order* on `[n]` is a transitively-closed, irreflexive, antisymmetric relation set; `(a,b)` in the set means `a ≺ b`. `PPF_n` is the poset of *proper* partial orders on `[n]` — relation set nonempty *and* non-total — ordered by refinement (relation-set inclusion); `|PPF_n| = 12, 194, 4110, …` at `n = 3, 4, 5, …`. `Δ_n := Δ(PPF_n)` is its order complex (the simplicial complex of chains of `PPF_n`). `S_n` permutes `[n]`; we regard `S_n ⊂ S_{n+1}` as the stabiliser of the element `n`, so `S_n` acts on both `PPF_n` and `PPF_{n+1}`. All (co)homology is reduced, `ℚ`-coefficients.

**The inclusion.** `ι_n : PPF_n ↪ PPF_{n+1}` is the *standard inclusion*: a partial order `x` on `[n]` is sent to the same relation set, now viewed on `[n+1]` with the new element `n` incomparable to all of `[n]` (F10 §1, F17 §1). It is an **order-ideal inclusion** — `y ⊆ ι_n(x)` and `y ∈ PPF_{n+1}` forces `y ∈ ι_n(PPF_n)`, because `n` isolated in `ι_n(x)` is inherited by every `y ⊆ ι_n(x)`. Hence `(Δ_{n+1}, Δ_n)` is a *good pair*: `ι_n` is a simplicial subcomplex inclusion, in particular a cofibration, so

$$\widetilde H^k(\Delta_{n+1},\Delta_n) \;=\; \widetilde H^k(\Delta_{n+1}/\Delta_n)\qquad\text{for all }k.$$

We write `ι_n` also for the induced simplicial inclusion `Δ_n ↪ Δ_{n+1}` and `ι_n(x)` for the relation set `x` viewed on `[n+1]`.

**The cofiber LES.** The long exact sequence of the pair `(Δ_{n+1}, Δ_n)` in reduced cohomology is exact for every `n` and every `k` — this is standard, requires *no hypothesis*:

$$\cdots \to \widetilde H^{k}(\Delta_{n+1}/\Delta_n) \xrightarrow{\ q_n\ } \widetilde H^{k}(\Delta_{n+1}) \xrightarrow{\ \iota_n^*\ } \widetilde H^{k}(\Delta_n) \xrightarrow{\ \delta_n\ } \widetilde H^{k+1}(\Delta_{n+1}/\Delta_n) \to \cdots \tag{LES}$$

`δ_n` is the pair connecting map; in degree `k = n−2` it is the subject of **(UCC.2)** (F10 §6.3, F15 §2).

**(UCC.2) and its reformulation.** (UCC.2)(n) is the statement that `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` is injective. By exactness of (LES) at `H̃^{n-2}(Δ_n)`,

$$\ker(\delta_n) \;=\; \operatorname{im}\bigl(\iota_n^* : \widetilde H^{n-2}(\Delta_{n+1}) \to \widetilde H^{n-2}(\Delta_n)\bigr),$$

so **`(UCC.2)(n) ⟺ ι_n^* = 0` on `H̃^{n-2}`** (F17 §7.3). Under `Hyp(n)`, `H̃^{n-2}(Δ_n) = sgn_{S_n}` is 1-dimensional and `ι_n^*` is `S_n`-equivariant; so `im(ι_n^*)` is an `S_n`-subrepresentation of a 1-dimensional space — *either `0` or all of `sgn_{S_n}`*. (UCC.2)(n) is precisely the assertion that it is `0`: "the inherited `sgn`-class of `Δ_n` dies in `Δ_{n+1}`."

### 1.1 The circularity guard — what F18 must avoid

The F10 cohomological-core induction is `Hyp(n) ∧ (UCC)(n) ⇒ Hyp(n+1)` (F10 §6.2–§6.3). So a proof of **(UCC.2)(n) must not assume `Hyp(n+1)`**: under `Hyp(n+1)`, `H̃^{n-2}(Δ_{n+1}) = 0` (concentration in degree `n−1 = (n+1)−2`), whence `ι_n^* = 0` *trivially* — and the whole induction collapses into a circle.

This is not a hypothetical danger. The `n = 3` base case (mg-59f3, recorded in F15 §4) proved `δ_3` injective exactly so: `ker(δ_3) = im(ι_3^*) = 0` *because the source `H̃^1(Δ_4) = 0`* — i.e. because `Hyp(4) = Hyp(n+1)` holds. That argument is correct at `n = 3` (`Hyp(4)` is a *proven* base fact) but is **structurally circular for general `n`** and does *not* generalise.

F18's argument (§§2–4) is of a completely different character: it exhibits an **explicit null-homotopy of `ι_n` built from poset data alone**, with no reference to the cohomology of `Δ_{n+1}` at all. It therefore proves `ι_n^* = 0` *without* knowing `H̃^{n-2}(Δ_{n+1}) = 0`. §4.2 verifies, step by step, that no hypothesis whatsoever enters — the proof is unconditional, so the circularity guard is discharged vacuously.

---

## §2. The map `κ_n` and the explicit poset zig-zag

### 2.1 The cone element `ω_n` and the cone map `κ_n`

> **Definition 2.1.** For `n ≥ 3`, let
> $$\omega_n \;:=\; \{(n, b) : b \in [n]\}$$
> — the relation set on `[n+1]` in which the new element `n` lies **below every element of `[n]`**, and `[n]` is an internal antichain. Define
> $$\kappa_n : PPF_n \longrightarrow \{\text{relation sets on } [n+1]\}, \qquad \kappa_n(x) \;:=\; x \,\cup\, \omega_n .$$

> **Lemma 2.2 (`ω_n` is a vertex of `Δ_{n+1}`).** *For every `n ≥ 3`, `ω_n ∈ PPF_{n+1}`.*

*Proof.* `ω_n` is transitively closed: its only relations are `(n,b)`, and there is no relation `(b,c)` with `b ∈ [n]` to compose with (the elements of `[n]` are pairwise incomparable in `ω_n`), nor any `(a,n)`. It is irreflexive and antisymmetric: `n` occurs only as a first coordinate. It is nonempty (`n ≥ 1`). It is non-total: `[n]` is an internal antichain with `n ≥ 3 ≥ 2` elements, so e.g. `0` and `1` are incomparable in `ω_n`. Hence `ω_n` is a proper partial order on `[n+1]`. ∎

> **Lemma 2.3 (`κ_n` is well-defined into `PPF_{n+1}`).** *For every `n ≥ 3` and every `x ∈ PPF_n`, `κ_n(x) = x ∪ ω_n ∈ PPF_{n+1}`. This is the one combinatorial obligation of F18.*

*Proof.* Fix `x ∈ PPF_n`. The union `x ∪ ω_n` is disjoint: `x` has only relations within `[n]`, `ω_n` only relations of the form `(n,·)`.

- **Transitively closed.** New composable pairs in `x ∪ ω_n`: a relation `(n,b) ∈ ω_n` followed by `(b,c) ∈ x` (`b,c ∈ [n]`) forces `(n,c)` — and `(n,c) ∈ ω_n` since `c ∈ [n]`. No relation has `n` as a *second* coordinate, so nothing composes *through* `n` on its left. Hence `x ∪ ω_n` is transitively closed (`x` itself already is).
- **Irreflexive, antisymmetric.** `x` is a partial order; `n` occurs in `ω_n` only as a first coordinate, creating no `(n,n)` and no 2-cycle. So `x ∪ ω_n` is a partial order on `[n+1]`.
- **Nonempty.** `x ≠ ∅`.
- **Non-total — the key point.** Suppose `x ∪ ω_n` were total on `[n+1]`. Comparability of two elements `a, c ∈ [n]` in `x ∪ ω_n` is comparability in `x` (every added relation involves `n`, not two elements of `[n]`). So `x ∪ ω_n` total would force `x` total on `[n]` — contradicting `x ∈ PPF_n`. Hence `x ∪ ω_n` is non-total.

Therefore `κ_n(x) ∈ PPF_{n+1}`. ∎

The harness ([C]) verifies Lemma 2.3 directly for **every** `x ∈ PPF_n` at `n = 3, 4` (membership in the materialised `PPF_{n+1}`) and at `n = 5` (the proper-partial-order property of `κ_5(x)` checked directly on `[6]`, without materialising `PPF_6`). Total: `12 + 194 + 4110` instances, all pass.

> **Lemma 2.4 (`κ_n` is `S_n`-equivariant and order-preserving).** *For every `n ≥ 3`:*
> *(a) `κ_n` is order-preserving: `x ⊆ x' ⟹ κ_n(x) ⊆ κ_n(x')`.*
> *(b) `κ_n` is `S_n`-equivariant: `g · κ_n(x) = κ_n(g · x)` for all `g ∈ S_n`.*

*Proof.* (a) `x ⊆ x'` gives `x ∪ ω_n ⊆ x' ∪ ω_n` immediately. (b) `g ∈ S_n` fixes `n` and permutes `[n]`, so `g · ω_n = {(n, g·b) : b ∈ [n]} = {(n,c) : c ∈ [n]} = ω_n` — `ω_n` is `S_n`-fixed. Hence `g · κ_n(x) = g·(x ∪ ω_n) = (g·x) ∪ ω_n = κ_n(g·x)`. ∎

### 2.2 The zig-zag

> **Proposition 2.5 (the zig-zag of comparable poset maps).** *For every `n ≥ 3`, the three poset maps `PPF_n → PPF_{n+1}`*
> $$\iota_n, \qquad \kappa_n, \qquad \mathrm{const}_{\omega_n} \;(:\; x \mapsto \omega_n)$$
> *are all order-preserving and `S_n`-equivariant, and satisfy, pointwise for every `x ∈ PPF_n`,*
> $$\iota_n(x) \;\le\; \kappa_n(x) \;\ge\; \omega_n = \mathrm{const}_{\omega_n}(x). \tag{$\ast$}$$

*Proof.* `ι_n` is the standard order-ideal inclusion — order-preserving and `S_n`-equivariant (`S_n` fixes `n`). `κ_n` is order-preserving and `S_n`-equivariant by Lemma 2.4, and lands in `PPF_{n+1}` by Lemma 2.3. `const_{ω_n}` is constant, hence trivially order-preserving, and `S_n`-equivariant because `ω_n` is `S_n`-fixed (Lemma 2.4 proof). The comparabilities (`∗`): `ι_n(x) = x ⊆ x ∪ ω_n = κ_n(x)`, and `ω_n ⊆ x ∪ ω_n = κ_n(x)`. Moreover *both inequalities are strict* — `κ_n(x) ⊋ x` since `ω_n ≠ ∅` and `ω_n ∩ x = ∅`, and `κ_n(x) ⊋ ω_n` since `x ≠ ∅` and `x ∩ ω_n = ∅`. ∎

The harness ([D]–[E]) verifies (`∗`) and the order-preservation/equivariance of all three maps exhaustively at `n = 3, 4` and on `S_5`-generators plus a comparable-pair sample at `n = 5`.

**Remark 2.6 (the dual cone).** By the order-reversal symmetry of `PPF`, the dual choice `ω_n' := {(b,n) : b ∈ [n]}` (the new element `n` *above* all of `[n]`) and `κ_n'(x) := x ∪ ω_n'` works identically, giving a second null-homotopy. We fix the "`n` below everything" cone throughout; nothing depends on the choice.

---

## §3. The null-homotopy theorem

### 3.1 The order-homotopy lemma

We use one standard fact of order-complex topology.

> **Lemma 3.1 (order-homotopy lemma; Björner, *Topological methods* §10; Kozlov, *CAT* Ch. 10; Quillen 1973 §1.3).** *Let `P, Q` be posets and `f, g : P → Q` order-preserving maps with `f(p) ≤ g(p)` for every `p ∈ P`. Then the induced maps of order complexes `|Δ(f)|, |Δ(g)| : |Δ(P)| → |Δ(Q)|` are homotopic. If `P, Q` carry a group action and `f, g` are equivariant, the homotopy is equivariant.*

*Proof (the prism, included for self-containedness).* Form the product poset `P × C` with `C = \{0 < 1\}`, and the map
$$h : P \times C \to Q, \qquad h(p,0) = f(p),\quad h(p,1) = g(p).$$
`h` is order-preserving: for `(p,i) ≤ (p',j)` in `P × C` (so `p ≤ p'`, `i ≤ j`) we need `h(p,i) ≤ h(p',j)`; the three cases are `f(p) ≤ f(p')` (✓, `f` monotone), `g(p) ≤ g(p')` (✓, `g` monotone), and — when `i=0,j=1` — `f(p) ≤ g(p')`, which holds because `f(p) ≤ f(p') ≤ g(p')`. The order complex of the product is a triangulation of the prism, `|Δ(P × C)| ≅ |Δ(P)| × [0,1]`, with `|Δ(P)| × \{0\}` and `× \{1\}` the two ends, on which `|Δ(h)|` restricts to `|Δ(f)|` and `|Δ(g)|`. So `|Δ(h)|` is a homotopy `|Δ(f)| ≃ |Δ(g)|`. Equivariance: if `f, g, h` are equivariant and the group acts trivially on `C`, `Δ(h)` is equivariant. ∎

Concretely, on chains, Lemma 3.1 is the **prism operator** `P_h : C_k(Δ(P)) → C_{k+1}(Δ(Q))`,
$$P_h(\,[x_0 < \cdots < x_k]\,) \;=\; \sum_{i=0}^{k} (-1)^i\,\bigl[\,h(x_0,0),\dots,h(x_i,0),\,h(x_i,1),\dots,h(x_k,1)\,\bigr],$$
satisfying the chain-homotopy identity `∂P_h + P_h∂ = g_\# − f_\#`. The harness ([H]) builds this operator explicitly for the two relevant `h`'s and verifies the identity on every simplex.

### 3.2 `ι_n` is null-homotopic

> **Theorem 3.2 (the null-homotopy theorem).** *For every `n ≥ 3`, the inclusion `ι_n : Δ_n ↪ Δ_{n+1}` is `S_n`-equivariantly null-homotopic:*
> $$|\iota_n| \;\simeq_{S_n}\; \mathrm{const}_{\omega_n}.$$
> *The null-homotopy is given by the explicit poset zig-zag (`∗`) of §2; it uses no `Hyp(m)`, no `(UCC)`, and no F17 result — it is unconditional.*

*Proof.* By Proposition 2.5, `ι_n ≤ κ_n` as order-preserving `S_n`-equivariant maps `PPF_n → PPF_{n+1}`. By Lemma 3.1, `|Δ(ι_n)| ≃_{S_n} |Δ(κ_n)|`. Again by Proposition 2.5, `const_{ω_n} ≤ κ_n` as order-preserving `S_n`-equivariant maps, so by Lemma 3.1, `|Δ(const_{ω_n})| ≃_{S_n} |Δ(κ_n)|`. Composing the two homotopies,
$$|\iota_n| \;\simeq_{S_n}\; |\kappa_n| \;\simeq_{S_n}\; |\mathrm{const}_{\omega_n}|,$$
and `|const_{ω_n}|` is the constant map at the vertex `ω_n` (a single point of `Δ_{n+1}`, `S_n`-fixed). Hence `ι_n` is `S_n`-equivariantly homotopic to a constant map — null-homotopic. Every ingredient (`ω_n ∈ PPF_{n+1}`, `κ_n` well-defined and monotone and equivariant, the comparabilities, Lemma 3.1) is established with no hypothesis on `Δ_n`, `Δ_{n+1}`, or the program; the conclusion is unconditional. ∎

**The chain-level form.** Combining the two prism operators of §3.1 — `P` for `ι_n ≃ κ_n` and `P'` for `const_{ω_n} ≃ κ_n` — gives an **explicit chain null-homotopy**
$$D \;:=\; P' - P \;:\; C_\ast(\Delta_n) \to C_{\ast+1}(\Delta_{n+1}), \qquad \partial D + D\partial \;=\; (\iota_n)_\# - \mathrm{const}_\# . \tag{3.3}$$
(`P'` collapses to its `i=0` term: `P'([x_0<\cdots<x_k]) = [\omega_n, \kappa_n(x_0),\dots,\kappa_n(x_k)]`, a cone on `κ_n` with apex `ω_n`.) The harness ([H]) builds `D` and verifies (3.3) on **every** simplex of `Δ_n` at `n = 3` (`24` simplices) and `n = 4` (`15 074` simplices), in exact integer arithmetic — a complete machine-certification of Theorem 3.2 at those levels.

**Geometric sanity check.** Under `Hyp(n)`, `Δ_n ≃_ℚ S^{n-2}`; the program's target `Hyp(n+1)` would give `Δ_{n+1} ≃ S^{n-1}`. The inclusion of a `(n−2)`-sphere into an `(n−1)`-sphere *is* null-homotopic — `π_{n-2}(S^{n-1}) = 0` for `n ≥ 3`. So Theorem 3.2 is exactly what the geometry predicts. The *content* of F18 is that the null-homotopy is produced **without** knowing the homotopy type of `Δ_{n+1}` — by an explicit poset cone, valid whatever `Δ_{n+1}` turns out to be. That is what makes it non-circular (cf. §1.1, §4.2).

---

## §4. The payoff — (UCC.2) for all `n`

### 4.1 `δ_n` injective

> **Theorem 4.1 ((UCC.2), unconditional).** *For every `n ≥ 3`:*
> *(i) `ι_n^* = 0` and `ι_{n,*} = 0` on `H̃^k`, `H̃_k` respectively, for every degree `k` (reduced, `ℚ`-coefficients);*
> *(ii) the connecting map `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` is **injective** — indeed `δ_k : H̃^k(Δ_n) → H̃^{k+1}(Δ_{n+1}/Δ_n)` is injective for every `k`.*
> *This is **(UCC.2)** for all `n`, proven unconditionally.*

*Proof.* (i) By Theorem 3.2, `ι_n` is null-homotopic. Reduced cohomology and homology are homotopy functors, and a constant map induces the zero map on `H̃^k`, `H̃_k` for all `k` (it factors through a point, and `H̃^k(\mathrm{pt}) = 0`). Hence `ι_n^* = 0` and `ι_{n,*} = 0` in every degree.

(ii) Apply exactness of the cofiber LES (§1, (LES)) at `H̃^k(Δ_n)`:
$$\widetilde H^{k}(\Delta_{n+1}) \xrightarrow{\ \iota_n^* = 0\ } \widetilde H^{k}(\Delta_n) \xrightarrow{\ \delta_k\ } \widetilde H^{k+1}(\Delta_{n+1}/\Delta_n).$$
Exactness gives `ker(δ_k) = im(ι_n^*) = 0`, so `δ_k` is injective. Taking `k = n−2` is (UCC.2)(n). The LES is exact for every `n, k` with no hypothesis; (i) is unconditional; so (ii) is unconditional. ∎

The harness ([H]) certifies Theorem 4.1 at `n = 3` — reproducing mg-59f3's `(UCC.2)@n=3` **by the non-circular route** (the chain null-homotopy `D`, not "`H̃^1(Δ_4)=0`") — and at `n = 4` (new). At `n = 5` the structural checks ([B]–[G]) confirm the zig-zag (`∗`) and the prism poset maps `H, H'` are order-preserving — i.e. the homotopy `ι_5 ≃ κ_5 ≃ const` exists as an explicit poset map — which *is* the proof of Theorem 3.2 at `n = 5`; the chain-level recomputation is omitted only because `Δ_5` is large, exactly as F17's harness omits the recomputation of large complexes.

### 4.2 The circularity guard, discharged

The proof of Theorem 4.1 is **unconditional**. We verify, step by step, that no hypothesis enters — in particular not `Hyp(n+1)`:

| Step | Statement | Inputs used |
|---|---|---|
| Lemma 2.2 | `ω_n ∈ PPF_{n+1}` | combinatorics of `[n+1]` only |
| Lemma 2.3 | `κ_n(x) ∈ PPF_{n+1}` for all `x ∈ PPF_n` | combinatorics only — transitivity, non-totality of `x` |
| Lemma 2.4 | `κ_n` order-preserving, `S_n`-equivariant | combinatorics only |
| Prop. 2.5 | the zig-zag `ι_n ≤ κ_n ≥ const_{ω_n}` | Lemmas 2.2–2.4 |
| Lemma 3.1 | order-homotopy lemma | standard topology — no hypothesis |
| Thm. 3.2 | `ι_n` null-homotopic | Prop. 2.5 + Lemma 3.1 |
| Thm. 4.1 | `ι_n^* = 0`, `δ_n` injective | Thm. 3.2 + exactness of (LES) — standard, unconditional |

No step invokes `Hyp(m)` for any `m`, `(UCC.1)` or `(UCC.2)` at any level, the F17 reduction, or any computation specific to a value of `n`. In particular **`Hyp(n+1)` is never used** — there is nothing to smuggle, because *nothing is assumed*. F18's proof of (UCC.2)(n) is logically prior to, and independent of, the entire F10 induction. This is the strongest possible resolution of the circularity guard: (UCC.2) is not merely "provable non-circularly within the induction" — it is *unconditionally true*, a fact about the absolute tower `(Δ_n)_n` that holds regardless of the induction.

**Contrast with the `n = 3` base case.** mg-59f3 / F15 §4 proved `δ_3` injective via `ker(δ_3) = im(ι_3^*) = 0` *because `H̃^1(Δ_4) = 0`* — i.e. via `Hyp(4) = Hyp(n+1)`. That route is correct at `n = 3` but circular for general `n` (§1.1). F18 proves the *same* conclusion `ι_3^* = 0` by the null-homotopy of `ι_3` — with no reference to `H̃^1(Δ_4)` — and the harness confirms the two routes agree at `n = 3`. F18 is genuinely the general-`n` argument, not an extrapolation of the `n = 3` accident.

---

## §5. Consequences — (UCC) complete, F10 core unconditional

### 5.1 The cofiber LES splits

> **Corollary 5.1.** *For every `n ≥ 3` and every `k`, the cofiber LES breaks into short exact sequences*
> $$0 \to \widetilde H^{k-1}(\Delta_n) \xrightarrow{\ \delta_{k-1}\ } \widetilde H^{k}(\Delta_{n+1}/\Delta_n) \xrightarrow{\ q_n\ } \widetilde H^{k}(\Delta_{n+1}) \to 0,$$
> *`S_n`-equivariantly; over `ℚ` it splits:*
> $$\widetilde H^{k}(\Delta_{n+1}/\Delta_n) \;\cong\; \widetilde H^{k-1}(\Delta_n) \,\oplus\, \widetilde H^{k}(\Delta_{n+1})\qquad\text{as }S_n\text{-representations.}$$

*Proof.* With `ι_n^* = 0` in all degrees (Thm. 4.1(i)), the LES `\cdots → H̃^{k}(Δ_{n+1}/Δ_n) \xrightarrow{q_n} H̃^{k}(Δ_{n+1}) \xrightarrow{0} H̃^{k}(Δ_n) \xrightarrow{δ} H̃^{k+1}(Δ_{n+1}/Δ_n) → \cdots` separates: `δ_{k-1}` is injective (Thm. 4.1(ii)) with image `ker(q_n) = im(δ_{k-1})`... — exactness at the three terms gives the displayed short exact sequence, which splits over `ℚ`. All maps are `S_n`-equivariant. ∎

### 5.2 (UCC) is complete

> **Corollary 5.2.** *The master hypothesis **(UCC)** of F10 §6.3 is proven for all `n ≥ 3`:*
> - ***(UCC.1)*** *— `H̃^k(Δ_{n+1}/Δ_n) = 0` for `k ≠ n−1` and `H̃^{n-1}(Δ_{n+1}/Δ_n) ≅ 2·sgn_{S_n}` — holds **⟺ `Hyp(n)`** (F17 Thm. 5.1), hence is discharged by the F10 induction hypothesis;*
> - ***(UCC.2)*** *— `δ_n` injective — holds **unconditionally** (F18 Thm. 4.1).*

This is immediate: F17 closes (UCC.1) ⟺ Hyp(n); F18 closes (UCC.2) outright.

**Consistency cross-check.** Corollary 5.1 and F17's reduction identity `H̃^k(Δ_{n+1}/Δ_n) ≅ 2·H̃^{k-1}(Δ_n)` (F17 Thm. 5.1) together give
$$2\cdot\widetilde H^{k-1}(\Delta_n) \;\cong\; \widetilde H^{k-1}(\Delta_n)\,\oplus\,\widetilde H^{k}(\Delta_{n+1})\quad\Longrightarrow\quad \widetilde H^{k}(\Delta_{n+1}) \;\cong\; \widetilde H^{k-1}(\Delta_n)\quad\text{as }S_n\text{-reps},$$
by cancellation of `ℚ S_n`-representations (Krull–Schmidt). This is exactly the degree-shift engine of the F10 inductive step (F10 §6.2): the absolute cohomology of `Δ_{n+1}` is, as an `S_n`-representation, the shift of that of `Δ_n`. At `n = 3` it reads `H̃^2(Δ_4) ≅ H̃^1(Δ_3) = sgn_{S_3}` and `H̃^2(Δ_4/Δ_3) ≅ H̃^1(Δ_3) ⊕ H̃^2(Δ_4) = 2·sgn_{S_3}` — recovering mg-6295's `B_3 = 2·sgn_{S_3}` and F14's `B_4 = 2·sgn_{S_4}` pattern. F18 and F17 fit together with no slack.

### 5.3 The F10 cohomological core is unconditional

> **Theorem 5.3 (the F10 cohomological core, now unconditional).** *`Hyp(n)` holds for every `n ≥ 3`. Equivalently: `Δ_n ≃_ℚ S^{n-2}` with `H̃^{n-2}(Δ_n;ℚ) ≅ sgn_{S_n}` for all `n ≥ 3` — (H-Cox) and (sgn) at general `n` — and the canonical class `ω_bal^{(n)}` exists, is unique up to scalar, and pairs `±1` with the canonical critical cell `c^*_n`.*

*Proof.* Induction on `n`. **Base:** `Hyp(3)` is rigorous (F10 §6.1: `Δ_3 ≃ S^1`, `H̃^1(Δ_3) = sgn_{S_3}`). **Step:** assume `Hyp(n)`. By F17 Theorem 5.1, `Hyp(n)` implies `(UCC.1)` at level `n`. By F18 Theorem 4.1, `(UCC.2)` at level `n` holds unconditionally. F10 §6.2 then gives `Hyp(n) ∧ (UCC.1)(n) ∧ (UCC.2)(n) ⇒ Hyp(n+1)`, gap-free. So `Hyp(n)` for all `n`. The `ω_bal^{(n)}` / pairing statements then follow as in F10 §6.6 (steps 1–3). ∎

The induction now reads, with **no free-standing conditional input**:
$$\mathrm{Hyp}(n)\ \xrightarrow[\text{F17 (UCC.1)⟺Hyp}]{}\ (\mathrm{UCC.1})@n\ \ \wedge\ \ (\mathrm{UCC.2})@n\ \xrightarrow[\text{F18, unconditional}]{}\ \text{[F10 §6.2]}\ \xrightarrow{}\ \mathrm{Hyp}(n+1).$$

### 5.4 What remains for the full width-3 theorem

F18 + F17 make the **cohomological core** unconditional (Theorem 5.3 — F10 conditional-theorem parts (i)–(ii)). The **numerical width-3 conclusion** (F10 §6.7 part (iii) — every width-3 poset `P` admits incomparable `x,y` with `Pr_P[x<_P y] ∈ [3/11, 8/11]`) additionally rests on two further inputs, *neither part of (UCC)* and *neither touched by F18*:

- **(ICOP-step)** (F10 §5.4) — verified `n = 3,4,5,6` (16/16 on canonical chains); reduces to one structurally-uniform lex-min cover step per `n` being BFT-sharp.
- **the width-3 reduction bridge** (F10 §7.3) — rigorous `m ≤ 4`; for `m ≥ 5` reduces to (ICOP-step) plus "the `ι`-tower meets every width-3 orbit."

These are F10 §7.4's two *narrower* conditional inputs — both verified `n ≤ 6`, both reduced to clean uniform sub-statements. F18 does not address them and does not claim to: its scope is **(UCC.2)**, hence **(UCC)**, hence the **cohomological core**. The precise post-F18 status: *the F10 cohomological core is unconditional; the full numerical width-3 theorem holds modulo (ICOP-step) + the width-3 bridge* (and, separately, the Lean 4-axiom in-tree trust surface — a formalization track, not a mathematical gap).

---

## §6. What F18 establishes and does not establish

### 6.1 Establishes

- **Theorem 3.2** — `ι_n : Δ_n ↪ Δ_{n+1}` is `S_n`-equivariantly null-homotopic, for every `n ≥ 3`, **unconditionally**, by the explicit poset zig-zag `ι_n ≤ κ_n ≥ const_{ω_n}` (`κ_n(x) = x ∪ ω_n`, the "cone `n` below everything" map). One load-bearing combinatorial lemma (Lemma 2.3: `κ_n` well-defined) plus the standard order-homotopy lemma.
- **Theorem 4.1** — `(UCC.2)` for all `n`: `ι_n^* = 0` in all degrees, hence `δ_n` injective in all degrees. **Unconditional** — no `Hyp(m)`, no `(UCC)`, no F17. The circularity guard is discharged vacuously (§4.2).
- **Corollary 5.2** — **(UCC) is complete**: (UCC.1) ⟺ Hyp(n) (F17), (UCC.2) unconditional (F18).
- **Theorem 5.3** — the **F10 cohomological core is unconditional**: `Hyp(n)` for all `n`; (H-Cox) + (sgn) at general `n`; `ω_bal^{(n)}` exists/unique with the `±1` pairing.
- **Corollary 5.1** — the cofiber LES splits: `H̃^k(Δ_{n+1}/Δ_n) ≅ H̃^{k-1}(Δ_n) ⊕ H̃^k(Δ_{n+1})` as `S_n`-reps; consistency with F17 gives `H̃^k(Δ_{n+1}) ≅ H̃^{k-1}(Δ_n)`, the degree-shift engine of the induction.
- **Verification harness** — `scripts/compat_geom_F18_ucc2_delta_injective.py`: `43 677` checks at `n = 3,4,5`, all pass, ≈ 2 s. `κ_n` well-defined and `S_n`-equivariant; the zig-zag (`∗`); the prism poset maps order-preserving; the explicit chain null-homotopy `∂D + D∂ = (ι_n)_\# − const_\#` on every simplex of `Δ_n` (`n = 3,4`, exact integers); homology anchor `Betti(Δ_3) = (0,1)`, `Betti(Δ_4) = (0,0,1,0,0)`.

### 6.2 Does NOT establish

- **F18 does not prove (ICOP-step) or the width-3 reduction bridge.** These are F10 §7.4's two secondary conditional inputs of the *numerical* width-3 conclusion (F10 part (iii)); they are not part of (UCC) and are outside F18's scope (§5.4). Both are verified `n ≤ 6` and reduced to clean uniform sub-statements in F10; closing them is separate work.
- **F18 does not recompute large complexes.** The chain-level certification (`∂D + D∂` on all simplices) is run at `n = 3, 4`; at `n = 5` the structural checks confirm the zig-zag and prism poset maps, which *is* the proof of Theorem 3.2 at `n = 5`. This matches `feedback_focus_on_induction_not_special_cases` — the result is n-uniform; the harness confirms the *hypotheses* of the n-uniform lemmas, it is not a datapoint hunt. No new HPC.
- **F18 does not touch the Lean trust surface.** No new axioms; no Lean changes. The in-tree `width3_one_third_two_thirds` artifact (the F10 4-axiom track) is a separate formalization concern, untouched.
- **F18 does not touch route (iii) / mg-b345.** It stays **PARKED**. The route-(iii) escalation was conditioned on the internal route *failing* to deliver (UCC); the internal route has now delivered both halves — (UCC.1) via F17, (UCC.2) via F18 — so the escalation trigger is, definitively, not met.

### 6.3 Why the argument is short — and why that is correct

F18's proof is short because F17 did the hard work. Before F17, (UCC.1) and (UCC.2) were tangled together inside the M1 (discrete-Morse / Forman-cancellation) and M2 (FI representation-stability) machinery — both genuinely hard, and route (ii) of M2 died (F16). F17's contribution was to *separate* the two: it proved (UCC.1) ⟺ Hyp(n) by an n-uniform equivariant cofiber Morse reduction, leaving (UCC.2) "as a question purely about the absolute tower `(Δ_n)_n` and the inclusion `ι_n`" (F17 §8.3). Once isolated like that, (UCC.2) *is* simply the question "is `ι_n` null-homotopic?" — and the absolute tower `PPF_n ↪ PPF_{n+1}` has exactly the room needed to answer it: the new element `n` can be coned below (or above) everything, giving an explicit null-homotopy with no input from the cohomology of `Δ_{n+1}`. The shortness is the *payoff* of F17's separation, not a sign that F18 is trivial: the content is precisely that the null-homotopy can be written down *without* assuming the homotopy type of `Δ_{n+1}` (§3.2, §4.2), which is what makes it non-circular and n-uniform.

---

## §7. Verdict, and the program after F18

### 7.1 Verdict: GREEN-ucc2-proven

Per the F18 verdict matrix: **GREEN-ucc2-proven** — *"(UCC.2) proven for all `n`, n-uniformly, non-circularly. (UCC) is COMPLETE; the F10 cohomological core is UNCONDITIONAL."* The verdict is the top branch: (UCC.2) is not merely advanced or reduced to a sub-statement (GREEN-partial), it is *closed* — and closed unconditionally, the strongest form. It is not AMBER-ucc2-stalls (the absolute-tower attack on `ι_n` did go n-uniform — Theorem 3.2 is a single n-independent construction). It is not RED-circularity-or-false (the argument is unconditional, hence non-circular by construction (§4.2); and `δ_n` injective is consistent with every established datapoint — mg-59f3 at `n = 3`, F15's `rank(∂_n) ≤ 1`, F17's reduction identity, and the harness's `n = 3, 4` certifications).

### 7.2 The program after F18

With F17 + F18, the **F10 cohomological core is unconditional** (Theorem 5.3). The general-`n` width-3 1/3-2/3 program now stands as:

- **Cohomological core (F10 parts (i)–(ii))** — `Hyp(n)` for all `n`, H-Cox + sgn at general `n`, `ω_bal^{(n)}` existence/uniqueness/pairing — **DONE, unconditional** (F10 §6 + F17 + F18).
- **Numerical width-3 conclusion (F10 part (iii))** — rests on **(ICOP-step)** and the **width-3 reduction bridge** (F10 §7.4), both verified `n ≤ 6` and reduced to clean uniform sub-statements. *Recommended next targets* — these are now the program's load-bearing open items, and they are narrow, combinatorial, and not representation-stability-flavoured.
- **Lean formalization track** — the in-tree 4-axiom artifact; a separate concern, untouched by the F11→F18 line.
- **Route (iii) / mg-b345** — stays **PARKED** (§6.2).

A polecat recommendation, for the PM to weigh: the next ticket should target **(ICOP-step)** (F10 §5.4) — it is the more central of the two remaining inputs, it gates the numerical interval `[3/11, 8/11]`, and F10 already reduced it to "one structurally-uniform lex-min cover step per `n` being BFT-sharp." The width-3 reduction bridge (F10 §7.3) is the natural sibling/follow-on. Both keep the program "finishing the induction internally" (Daniel directives) — neither needs external collaboration or new HPC.

### 7.3 Trust-surface impact

**None.** F18 introduces no new axioms, makes no Lean changes, runs no HPC. It is order-complex topology — the order-homotopy lemma applied to one explicit `S_n`-equivariant poset zig-zag (Theorem 3.2), plus the standard cofiber LES (Theorem 4.1) — building on F17 (the transparent cofiber side), F10 (the induction structure), and mg-59f3 (the `n = 3` base, here recovered by the non-circular route). The verification harness is pure-Python stdlib, ≈ 2 s, `43 677` checks, all pass. The in-tree Lean artifact and the general-`n` paper-level track are untouched.

---

## §8. References

### 8.1 Predecessor and sibling mg-tickets

- **mg-4d3a** — F17 (option 3 — n-uniform `S_n`-equivariant cofiber Morse): **GREEN-equivariant-uniform.** `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`, `docs/state-F17.md`, `scripts/compat_geom_F17_equivariant_morse.py`. §5 (Theorem 5.1 — `(UCC.1) ⟺ Hyp(n)`, the reduction identity `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)`), §7.3 (**the (UCC.2) handle — `ι_n^* = 0` form — F18's mandate**), §8.2 (status table), §8.3 (**F18 recommended: attack `ι_n` directly**). **Parent.**
- **mg-8216** — F10 (general-`n` unified proof synthesis): **GREEN-conditional.** `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. §6.1 (`Hyp(n)`), §6.2 (the inductive step — consumes (UCC.1) + (UCC.2)), §6.3 (**(UCC)** — the master hypothesis; the conditional cohomological-core theorem), §6.4 ((UCC.2) phrased as cross-boundary Forman cancellation), §6.6 (core ⇒ width-3), §6.7 (the conditional theorem, final form), §7.3–§7.4 ((ICOP-step) + width-3 bridge — the secondary inputs of part (iii)).
- **mg-59f3** — PCR-2 / F8″″ (spectral-sequence `E_2` at `PPF_3 ↪ PPF_4`): `(UCC.2)` at `n = 3` — `δ_3` injective. F18 recovers this by the non-circular route (§4.2); mg-59f3's original argument used `H̃^1(Δ_4) = 0`, i.e. `Hyp(4) = Hyp(n+1)`, which does not generalise.
- **mg-f893** — F16 (route (ii) weaker form): **AMBER-route-ii-stalls.** `docs/compatibility-geometry-F16-central-stability-presentation.md`. §5 ((UCC.2) is **independent** of the route-(ii) mechanism — F18 confirms this from the other side: (UCC.2) is unconditional, downstream of nothing).
- **mg-8355** — F15 (`E_2`): **AMBER-partial3-not-iso.** `docs/compatibility-geometry-F15-e2-partial-test.md`. §4 (the `n = 3` cofiber LES — `ker(δ_3) = im(ι_3^*) = 0` *because the source is `0`*, the circular-for-general-`n` route F18 replaces), §6 (`∂_n` iso ⟺ `δ_n = 0` — so `(UCC.2)(n) ⇒ ∂_n` not iso; consistent with F18: `δ_n` injective, hence `≠ 0`, for all `n`).
- **mg-3839** — F14 (PCR-Lit-2′): **GREEN-cofiber-perfect.** `docs/compatibility-geometry-F14-pcr-lit2prime.md`. `B_4 = 2·sgn_{S_4}` — recovered by Corollary 5.1 + F17.
- **mg-6295** — PCR-Lit-2 / M1: discrete Morse on the cofiber. `B_3 = 2·sgn_{S_3}` — recovered by Corollary 5.1 + F17.
- **mg-ecf6** — F13: **GREEN-functoriality-established.** The good-pair / pair-LES conventions used in §1.
- **mg-b352** — F11: **GREEN-route-traction.** Route (i) closed-negative; route (iii) parked.
- **mg-b345** — F8″: route (iii), **PARKED** — F18 does not touch it; the escalation trigger is definitively not met (§6.2).

### 8.2 Mathematical literature

- A. Björner, *Topological methods*, in *Handbook of Combinatorics* (R. Graham, M. Grötschel, L. Lovász eds.), Elsevier, 1995, §10 — order-complex topology; the **order-homotopy lemma**: order-preserving `f, g : P → Q` with `f ≤ g` pointwise induce homotopic maps `|Δ(f)| ≃ |Δ(g)|` (§10.2); equivariant when `f, g` are.
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer, 2008, Ch. 10 (the order-homotopy / poset-map homotopy machinery; the prism operator) and Ch. 13.
- D. Quillen, *Higher algebraic K-theory I*, LNM 341 (1973), §1.3 — comparable functors / poset maps induce homotopic maps of nerves (the order-homotopy lemma in its original form).
- A. Hatcher, *Algebraic Topology*, Cambridge, 2002, §2.1 — the prism operator and the chain-homotopy identity `∂P + P∂ = g_\# − f_\#`; §2.2 — the long exact sequence of a good pair, naturality, homotopy invariance.

### 8.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (F18 is pure internal structural mathematics — one explicit poset construction plus the standard order-homotopy lemma. Route (iii)/mg-b345 stays parked, its escalation trigger definitively unmet — §6.2, §7.2.)
- 2026-05-14T08:05Z — focus on the induction, not special cases. (F18's content is *entirely* n-uniform: Theorems 3.2, 4.1 and Lemmas 2.2–2.5 are general-`n` statements with single n-independent proofs. The `n = 3,4,5` harness checks the *hypotheses* of those n-uniform lemmas — a trip-wire, not a datapoint hunt; no new HPC, no new `n`-datapoints.)

---

*F18 (mg-d039), Session 1 — verdict GREEN-ucc2-proven. `ι_n : Δ_n ↪ Δ_{n+1}` is null-homotopic for every `n ≥ 3` (explicit `S_n`-equivariant poset zig-zag, unconditional), so `δ_n` is injective: **(UCC.2)** holds for all `n`. With F17 ((UCC.1) ⟺ Hyp(n)), **(UCC) is COMPLETE** and the **F10 cohomological core is UNCONDITIONAL** (Theorem 5.3). The numerical width-3 conclusion additionally rests on (ICOP-step) + the width-3 bridge (F10 §7.4) — the recommended next targets. No new axioms; no Lean changes.*
