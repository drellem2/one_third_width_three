# Compat-Geom — F17: the n-uniform S_n-equivariant cofiber discrete Morse — (UCC.1) reduced to Hyp(n) (mg-4d3a)

**Branch:** `compat-geom-F17-nuniform-equivariant-morse` (new).
**Parent:** mg-f893 (F16, AMBER-route-ii-stalls) §7.3 (the recommended pivot); mg-8355 (F15) §7.3 option 3 (where the pivot was first documented).
**Chain:** mg-b352 (F11) → mg-ecf6 (F13) → mg-3839 (F14) → mg-8355 (F15) → mg-f893 (F16) → **mg-4d3a (F17)**.
**Type:** Structural argument (equivariant discrete Morse theory / order-complex topology), with a light verification harness re-confirming the construction at n = 3, 4, 5. LaTeX-style Markdown; **no new axioms; no Lean changes.** Multi-session-able; cumulative state ledger in `docs/state-F17.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: GREEN-equivariant-uniform.** Option 3 closes. F14's S_n-equivariant order-ideal reduction of the cofiber `Δ_{n+1}/Δ_n` is **n-uniform**: its three steps (MoveA / MoveB / PEEL) have hypotheses that hold for *every* `n ≥ 3` by n-independent arguments, and each step is S_n-equivariant by construction. The reduction's terminal complex `Δ(A_n)` satisfies an S_n-equivariant homology isomorphism

$$\boxed{\ \widetilde H_\ast(\Delta(A_n)) \;\cong\; \widetilde H_\ast(\Delta_n)\quad\text{as }S_n\text{-representations, for all }n\ge 3,\ \text{unconditionally.}\ }$$

Combined with the (unconditional, n-uniform) reduction identity `H̃_d(Δ_{n+1}/Δ_n) = 2·H̃_{d-1}(Δ(A_n))`, this gives

$$\widetilde H_d(\Delta_{n+1}/\Delta_n)\;\cong\;2\cdot\widetilde H_{d-1}(\Delta_n)\qquad\text{as }S_n\text{-representations, for all }n\ge3,\ \text{unconditionally.}$$

Therefore **(UCC.1) at level n is equivalent to Hyp(n)** — the F10 cohomological-core inductive hypothesis. (UCC.1) is no longer an independent conditional input: it is *discharged by the induction itself*. The cofiber-Morse matching `M_rel` is perfect with critical vector `(0,…,0,2,0)` and its 2 critical `(n−1)`-cells carry `2·sgn_{S_n}` — **for every n**, given Hyp(n). All three F17 sub-questions (equivariance / perfection / representation type, n-uniformly) close. With the F10 cohomological core, the **only** remaining conditional input of (UCC) is **(UCC.2)** (δ_n injective for general n).

**Deliverables:**
- `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md` (this doc).
- `docs/state-F17.md` (cumulative state ledger).
- `scripts/compat_geom_F17_equivariant_morse.py` — verification harness: re-confirms, at n = 3, 4, 5, every n-uniform structural lemma below; checks the `(Q,F)` model of `A_n` agrees with F14's direct definition (n = 3, 4: exact set equality, `|A_3| = 66`, `|A_4| = 1420`); reproduces `H̃_∗(Δ(A_3)) = H̃_∗(Δ_3)` with matching equivariant type (`sgn`). Pure-Python stdlib, runtime ≈ 46 s. All 21 checks pass.

---

## §0. Executive summary

### 0.1 The pivot — where F17 stands in the program

The (FG-Cofiber) attack on (UCC.1)'s representation-type half had three routes (F10 §7.2.d). After F16:

- **Route (i)** (chamber-quotient finite ambient): **closed-negative** (F11 — chamber cell count super-exponential, not a finitely generated FI-module).
- **Route (ii)** (degree-shift-aware cofiber-cohomology object, FI / central stability): **closed-negative** (F16 — `∂_{n+1}∘∂_n = 0` unconditionally forces unbounded generation degree; no bounded central-stability presentation exists; route (ii) *reproduces* (FG-Cofiber) rather than reducing it).
- Both founder on the same rock: `(sgn_{S_n})_n` is not a finitely generated FI-module.
- **Route (iii)** (mg-b345, Quillen-fiber): **PARKED**. F17 does not touch it.

F16 §7.3 / F15 §7.3 recommended **option 3**: instead of routing the representation-type half of (UCC.1) through a degree-shift FI object (route (ii), dead), compute it **directly per n** via an **S_n-equivariant** version of M1's cofiber discrete Morse. The evidence this is the right pivot: **F14 already did exactly this at n = 4** — an S_4-equivariant order-ideal reduction computed `B_4 = H̃³(Δ_5/Δ_4) = 2·sgn_{S_4}` directly, and mg-6295 did n = 3. F16 framed option 3 as *"an upgrade of M1 rather than a new mechanism"*. **F17 establishes the n-uniformity of that upgrade.**

### 0.2 What F17 proves

F14's reduction has a three-step shape (F14 §1):

> `Δ_{n+1}/Δ_n` —[MoveA: peel element n]→ `C_∗(Δ(R), Δ(R\Q_∅))` —[MoveB: the Type-∅ ideal]→ `H̃_{∗-1}(Δ(D_n)) ⊕ H̃_{∗-1}(Δ(U_n))` —[PEEL: the all-cone `Up_n` peel]→ `2·H̃_{∗-1}(Δ(A_n))`,

with `A_n := {x ∈ PPF_{n+1} : Down_n(x) ≠ ∅, Up_n(x) = ∅, x|_{[n]} ≠ ∅}` and the factor 2 coming from the `Down_n / Up_n` order-reversal duality (an S_n-equivariant isomorphism `D_n ≅ U_n`). F14 ran this *identically* at n = 3 → 4 and n = 4 → 5, but verified each level's collapse hypotheses **computationally** (F14 §4.2): *"each level's collapse hypotheses are re-verified computationally, not assumed."* That computational re-verification is exactly the gap F17 closes.

**F17's results, all n-uniform:**

1. **The reduction is n-uniform and S_n-equivariant (§2).** MoveA, MoveB, and PEEL are defined by *n-independent rules* built entirely from S_n-canonical data (peel element `n`, which `S_n` fixes; the Type-∅ ideal; the `Down/Up` duality; the operator `kill_up_n`). Their collapse hypotheses hold for **every n ≥ 3** by n-independent arguments (Lemma L1 + Boolean-lattice cones + a single interior operator) — *not* by per-n computation. Each step is an S_n-equivariant acyclic matching; the cluster lemma / patchwork theorem assembles them into a global S_n-equivariant acyclic cofiber matching `M_rel^{eq}`.

2. **Lemma L1 (§3) — the one load-bearing lemma.** For a chain (total order) `Q_0` on `[n]`, `n ≥ 3`, the poset `{Q : ∅ ≠ Q ⊊ Q_0}` of nonempty proper sub-partial-orders has **contractible** order complex. Proof: the closure operator `c(Q) = tc(Q ∪ {(a_1, a_n)})` lands in the poset and its image has a global minimum `{(a_1, a_n)}` — a cone. *This single lemma powers both the MoveA fibre hypothesis and the `A_n` analysis.*

3. **The terminal complex (§4): `Δ(A_n) ≃_{S_n} Δ_n`.** Modelling `A_n` as pairs `(Q, F)` (a nonempty partial order `Q` on `[n]` plus a nonempty filter `F`), the non-total-restriction part `A_n^{nt}` is an order ideal carrying the **S_n-equivariant closure operator** `c(Q, F) = (Q, [n])`, whose image is `≅ PPF_n`; so `Δ(A_n^{nt}) ≃_{S_n} Δ(PPF_n) = Δ_n`. The total-restriction filter `A_n^t` attaches along **contractible down-sets** (Lemma L1 again, by induction on the filter). Hence the S_n-equivariant inclusion `Δ(A_n^{nt}) ↪ Δ(A_n)` is a homology isomorphism, and `H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)` as S_n-representations.

4. **The payoff (§5): (UCC.1) ⟺ Hyp(n).** Assembling: `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` as S_n-representations, **unconditionally, for all n ≥ 3**. So under Hyp(n) — `H̃^k(Δ_n) = sgn_{S_n}` for `k = n−2`, else `0` — the cofiber is `2·sgn_{S_n}` concentrated in degree `n−1`: precisely **(UCC.1)**. Conversely (UCC.1) forces Hyp(n). (UCC.1) is **not** an independent hypothesis; it is the inductive hypothesis re-expressed through the equivariant cofiber-Morse reduction.

### 0.3 What this means for the program

F10's cohomological core is the induction `Hyp(n) ⇒ Hyp(n+1)`, whose inductive step (F10 §6.2) consumes **(UCC.1)** and **(UCC.2)** at level n. F17 shows (UCC.1) at level n *is* Hyp(n) — so it is supplied for free by the induction hypothesis. The induction now reads:

> `Hyp(n)` —[F17: equivariant cofiber Morse]→ `(UCC.1) at level n` —[+ (UCC.2) at level n, F10 §6.2]→ `Hyp(n+1)`.

**The only remaining conditional input of the entire F10 cohomological core is (UCC.2): the connecting map `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` is injective.** This is a major narrowing. F17 does **not** close (UCC.2) (and was not asked to — the ticket: *"leaving only (UCC.2)"*); §7.3 records precisely why (UCC.2) is genuinely independent of the F17 mechanism, and §8.2 records the surviving handle.

### 0.4 The verdict in one line

> **The S_n-equivariant cofiber discrete Morse mechanism is n-uniform.** F14's order-ideal reduction is not an n = 4 coincidence: it is the n = 4 instance of an n-independent, S_n-equivariant construction whose every hypothesis is proven for all `n ≥ 3`. It yields `H̃_∗(Δ_{n+1}/Δ_n) ≅ 2·H̃_{∗-1}(Δ_n)` as S_n-representations, unconditionally — hence **(UCC.1) ⟺ Hyp(n)**, both halves (concentration *and* representation type), for all n. (UCC.1) is proven for all n; with the F10 core, only (UCC.2) remains.

---

## §1. Setting and the object (recap)

**Notation** (F1-refined / F2 / F5 / mg-6295 / F13 §0 / F14 §0.2). `[n] = {0,…,n−1}`. `PPF_n` is the poset of *proper* partial orders on `[n]` — non-empty relation set, non-total — ordered by refinement (relation-set inclusion); `|PPF_n| = 12, 194, 4110, …` at `n = 3, 4, 5, …`. `Δ_n := Δ(PPF_n)` is its order complex. `ι_n : PPF_n ↪ PPF_{n+1}` is the standard inclusion (element `n` incomparable to all of `[n]`) — an **order-ideal** inclusion, so `(Δ_{n+1}, Δ_n)` is a good pair. All (co)homology reduced, `ℚ`-coefficients. `S_n` permutes `[n]` and fixes `n`.

**Convention for relations.** We write a strict partial order as a transitively-closed, irreflexive relation set; `(a, b)` in the set means `a ≺ b`. (This matches `scripts/compat_geom_cofiber_morse_n4n5.py`.) For `x` a partial order on `[n+1]`:

- `x|_{[n]} := {(a, b) ∈ x : a, b ∈ [n]}` — the restriction to `[n]`.
- `Down_n(x) := {b : (n, b) ∈ x}` — what `n` lies *below*.
- `Up_n(x) := {a : (a, n) ∈ x}` — what `n` lies *above*.

**The cofiber object** (F11 §4.2, F13 §1.3, F14 §0.1). `B_n := H̃^{n-1}(Δ_{n+1}/Δ_n)` — the cofiber-cohomology diagonal. mg-6295: `B_3 = 2·sgn_{S_3}`; F14: `B_4 = 2·sgn_{S_4}`. (UCC.1) is the n-uniform statement that `H̃^∗(Δ_{n+1}/Δ_n)` is concentrated in degree `n−1` and equal to `2·sgn_{S_n}` there.

**The F14 reduction (the template).** F14 §1.2 collapses the relative complex `C_∗(Δ_{n+1}, Δ_n)` through three operations, each a rigorous statement about order-ideal filtrations / cluster-lemma matchings, ending at the *terminal complex*

$$A_n \;:=\; \{x \in PPF_{n+1} \;:\; Down_n(x) \ne \varnothing,\ Up_n(x) = \varnothing,\ x|_{[n]} \ne \varnothing\},$$

with the equality `H̃_d(Δ_{n+1}/Δ_n) = 2·H̃_{d-1}(Δ(A_n))` of S_n-representations (F14 §1.2, §2.2). F14 verified at `n = 3, 4` that `Δ(A_n) ≃ S^{n-2}` carrying `sgn_{S_n}`, giving `B_n = 2·sgn_{S_n}`. F17's task: prove the reduction and the terminal-complex statement n-uniformly.

### 1.1 The `(Q, F)` model of `A_n`

The first move is to give `A_n` a clean combinatorial model that exposes its structure.

> **Lemma 1.1 (the `(Q, F)` model).** *There is an S_n-equivariant poset isomorphism*
> $$A_n \;\xrightarrow{\ \cong\ }\; \bigl\{(Q, F) \;:\; Q\ \text{a nonempty partial order on}\ [n],\ F\ \text{a nonempty filter of}\ Q,\ \neg(F = [n]\ \wedge\ Q\ \text{total})\bigr\},$$
> *the target ordered by componentwise refinement `(Q, F) ≤ (Q', F') ⟺ Q ⊆ Q' ∧ F ⊆ F'`. The isomorphism is `x ↦ (x|_{[n]},\ Down_n(x))` with inverse `(Q, F) ↦ Q ∪ {(n, b) : b ∈ F}`. Here a* filter *of `Q` is an up-set: `b ∈ F`, `(b, c) ∈ Q ⟹ c ∈ F`.*

*Proof.* Let `x ∈ A_n`. Since `Up_n(x) = ∅`, element `n` appears in `x` only as a first coordinate, so `x = x|_{[n]} ∪ {(n, b) : b ∈ Down_n(x)}`. Set `Q := x|_{[n]}` and `F := Down_n(x)`. Then `Q ≠ ∅` (the condition `x|_{[n]} ≠ ∅`) and `F ≠ ∅` (the condition `Down_n(x) ≠ ∅`). Transitivity of `x`: if `(n, b) ∈ x` and `(b, c) ∈ x` with `b, c ∈ [n]` then `(n, c) ∈ x`; i.e. `F` is up-closed under `Q` — a filter. Conversely, for any such pair `(Q, F)`, the set `x := Q ∪ {(n, b) : b ∈ F}` is transitively closed (`F` a filter handles the only new composable pairs; no `(·, n)` relations exist, so nothing composes *through* `n`), irreflexive and antisymmetric (`n` occurs only as a first coordinate, creating no cycle). So `x` is a partial order on `[n+1]`. It is non-empty (`Q ≠ ∅`). It is non-total iff *not* every pair is comparable: the pair `{n, b}` for `b ∈ [n]` is comparable iff `b ∈ F`, and pairs inside `[n]` are governed by `Q`; so `x` is total iff `F = [n]` and `Q` is total — excluded by hypothesis. Hence `x ∈ PPF_{n+1}`, and `Down_n(x) = F ≠ ∅`, `Up_n(x) = ∅`, `x|_{[n]} = Q ≠ ∅`, so `x ∈ A_n`. The two maps are mutually inverse and clearly order-preserving in both directions: `x ⊆ x' ⟺ Q ⊆ Q' ∧ F ⊆ F'`. Equivariance: `g ∈ S_n` fixes `n`, so `g·x = g·Q ∪ {(n, g·b) : b ∈ F}`, i.e. `g·(Q, F) = (g·Q, g·F)`. ∎

The verification harness builds `A_n` *both* ways — via the `(Q, F)` model and via F14's direct definition `[x ∈ PPF_{n+1} : Down_n ≠ ∅, Up_n = ∅, x|_{[n]} ≠ ∅]` — and confirms exact set equality at `n = 3` (`|A_3| = 66`) and `n = 4` (`|A_4| = 1420`), matching F14's reported cardinalities.

### 1.2 The two pieces of `A_n`

Write, using the `(Q, F)` model,

$$A_n^{nt} := \{(Q, F) \in A_n : Q\ \text{non-total}\},\qquad A_n^{t} := \{(Q, F) \in A_n : Q\ \text{total}\}.$$

> **Lemma 1.2.** *`A_n^{nt}` is an order ideal (down-set) of `A_n`, and `A_n^{t}` is the complementary order filter. Both are S_n-invariant.*

*Proof.* If `(Q, F) ≤ (Q', F')` then `Q ⊆ Q'`; if `Q'` is non-total then so is the smaller `Q`. So `A_n^{nt}` is downward closed. `S_n` permutes `[n]` and "total" is S_n-invariant, so both pieces are S_n-invariant. ∎

In the `(Q, F)` model, for `(Q, F) ∈ A_n^{t}`: `Q` is total, so the properness condition `¬(F = [n] ∧ Q total)` forces `F ⊊ [n]`. A total order `Q` on `[n]` has exactly the nested nonempty proper filters `F_1 ⊊ F_2 ⊊ ⋯ ⊊ F_{n-1}` (`F_k` = the top `k` elements of the chain). So `A_n^t` decomposes, over the `n!` total orders, into "fibres" each a chain of length `n−1`.

---

## §2. The reduction is n-uniform and S_n-equivariant

The F14 reduction is the composite of three operations. We show each is governed by an *n-independent rule* and that its collapse hypothesis holds *for every `n ≥ 3`* by an n-independent argument. Throughout, "S_n-equivariant" means: the rule commutes with the S_n-action, because every piece of data it names (`element n`, `Down/Up`, `kill_up_n`, the Type-∅ ideal) is S_n-canonical.

### 2.1 MoveA — peel element `n`

**The rule.** `MoveA` takes the cofiber `Δ(P)/Δ(Q)` of an order-ideal pair and the *largest-labelled element* `e` present, here `e = n`; it produces the cofiber `C_∗(Δ(R), Δ(R\Q_∅))` where `R := P \ Q` and `Q_∅ := {x ∈ R : Q_{<x} = ∅}` (F14 §1.1). Element `n` is S_n-fixed, so the rule is S_n-equivariant. **Collapse hypothesis (F14 §1.1):** for every `x ∈ R`, the down-set `Q_{<x} := {y ∈ Q : y ⊊ x}` has `Δ(Q_{<x})` contractible-or-empty.

Here `P = PPF_{n+1}`, `Q = ι_n(PPF_n)` (the order ideal `Δ_n`), `R = PPF_{n+1} \ ι_n(PPF_n)`.

> **Proposition 2.1 (MoveA, n-uniform).** *For every `n ≥ 3` and every `x ∈ R`, `Δ(Q_{<x})` is contractible or empty.*

*Proof.* An element `y ∈ ι_n(PPF_n)` is a partial order on `[n+1]` with `n` isolated and `y|_{[n]} ∈ PPF_n`. So `y ⊆ x ⟺ y ⊆ x|_{[n]}` (identifying `y` with the relation set `y|_{[n]}`), and the down-set is

$$Q_{<x} \;\cong\; \{y : \varnothing \ne y \subseteq x|_{[n]},\ y\ \text{non-total on}\ [n]\}\ \setminus\ \{x|_{[n]}\ \text{if}\ n\ \text{isolated in}\ x\}.$$

Three cases on `x|_{[n]}`:

- **`x|_{[n]} = ∅`.** No nonempty `y ⊆ ∅`: `Q_{<x} = ∅`. (These `x` form `Q_∅`.)
- **`x|_{[n]}` nonempty, non-total.** Then `x|_{[n]} ∈ PPF_n`, so `n` is *not* isolated in `x` (else `x ∈ ι_n(PPF_n)`, not in `R`); hence the "if `n` isolated" deletion does not fire, and `x|_{[n]}` itself is the **global maximum** of `Q_{<x}`. A poset with a maximum has a contractible (cone) order complex.
- **`x|_{[n]}` total.** Then the non-total constraint deletes exactly the top element, and (whether or not `n` is isolated — if it is, the "if isolated" deletion removes the same `x|_{[n]}`) we get `Q_{<x} ≅ {y : ∅ ≠ y ⊊ x|_{[n]}}` with `x|_{[n]}` a chain on `[n]`. This is **contractible by Lemma L1** (§3), since `n ≥ 3`.

In every case `Δ(Q_{<x})` is contractible or empty. ∎

The harness checks Prop. 2.1 *directly* against the actual down-sets for every `x ∈ R` at `n = 3` (`|R| = 182`: 14 empty, 132 cone, 36 L1) and `n = 4` (`|R| = 3916`: 30 empty, 3646 cone, 240 L1), and via the structural census over `Pos_n` at `n = 5`.

**Output of MoveA.** `Q_∅ = {x ∈ R : x|_{[n]} = ∅}` is the "Type-∅" ideal, and `Sub := R \ Q_∅` is an order *filter* of `R`. F14 §1.1: `H̃_d(Δ_{n+1}/Δ_n) = H̃_d(Δ(R)/Δ(Sub_c))` where `Sub_c` is the complementary picture; concretely the cofiber is re-expressed with `S := Q_∅` as the new (ideal) subcomplex.

### 2.2 MoveB — the Type-∅ ideal splits into two Boolean cones

**The rule.** `MoveB` takes a cofiber `Δ(P)/Δ(Sub)` with `Sub` an order *filter*, `S := P \ Sub` the complementary ideal; it produces `⊕_j H̃_{d-1}(Δ(P^{(j)}))` summed over the connected components `S^{(j)}` of `Δ(S)`, with `P^{(j)} := {x ∈ Sub : S^{(j)}_{<x} ≠ ∅}` (F14 §1.1). **Collapse hypothesis:** for every component `S^{(j)}` and every `x ∈ Sub`, `Δ(S^{(j)}_{<x})` is contractible-or-empty.

Here `S = Q_∅ = {x ∈ PPF_{n+1} : x|_{[n]} = ∅,\ x ≠ ∅}` — partial orders whose *only* relations are between `n` and `[n]`.

> **Proposition 2.2 (MoveB, n-uniform).** *For every `n ≥ 3`: `Δ(S)` has exactly two connected components,*
> $$S_\downarrow := \{x \in S : Down_n(x) \ne \varnothing\} \cong B_{[n]}\setminus\{\varnothing\},\qquad S_\uparrow := \{x \in S : Up_n(x) \ne \varnothing\} \cong B_{[n]}\setminus\{\varnothing\},$$
> *(`B_{[n]}` the Boolean lattice of subsets of `[n]`), exchanged by the order-reversal involution `(a,b)↦(b,a)`; and for every `x ∈ Sub`, `S_\downarrow{}_{<x}` and `S_\uparrow{}_{<x}` are Boolean intervals — contractible (a cone) or empty.*

*Proof.* For `x ∈ S`, `x|_{[n]} = ∅`, so every relation of `x` is `(n, b)` or `(a, n)`. If both `(a, n)` and `(n, b)` were present, transitivity gives `(a, b) ∈ x|_{[n]} = ∅` — impossible. So `n` is related to `[n]` in *one direction only*: `S = S_\downarrow ⊔ S_\uparrow`, and `S_\downarrow ≅ {Down_n(x) : ∅ ≠ Down_n(x) ⊆ [n]} = B_{[n]} \setminus \{∅\}` (a relation set `{(n, b) : b ∈ T}` is transitively closed for *any* `T ⊆ [n]`, since there is nothing to compose), likewise `S_\uparrow`. These are two distinct connected components (no relation set in `S_\downarrow` is comparable to one in `S_\uparrow`: comparability would require one contained in the other, but they share no relations). The order-reversal involution swaps them S_n-equivariantly. For `x ∈ Sub`, `S_\downarrow{}_{<x} = {y ∈ S_\downarrow : y ⊊ x} ≅ {T : ∅ ≠ T ⊆ Down_n(x)}`, a Boolean interval: if `Down_n(x) ≠ ∅` it has maximum `Down_n(x)` (a cone, contractible), else it is empty. Symmetrically for `S_\uparrow`. ∎

The harness confirms `|S| = 14` (components `7+7`) at `n = 3` and `|S| = 30` (components `15+15`) at `n = 4`, with every fibre a Boolean cone, and the structural statement at `n = 5`.

**Output of MoveB.** `P^{(\downarrow)} = {x ∈ Sub : Down_n(x) ≠ ∅} =: D_n` and `P^{(\uparrow)} = {x ∈ Sub : Up_n(x) ≠ ∅} =: U_n`, so

$$H̃_d(Δ_{n+1}/Δ_n) \;=\; H̃_{d-1}(Δ(D_n)) \;\oplus\; H̃_{d-1}(Δ(U_n)).$$

The order-reversal involution restricts to an **S_n-equivariant isomorphism `D_n ≅ U_n`** (it commutes with `S_n`, which fixes `n`), so the two summands are isomorphic *as S_n-representations*:

$$H̃_d(Δ_{n+1}/Δ_n) \;\cong\; 2 \cdot H̃_{d-1}(Δ(D_n))\qquad\text{as }S_n\text{-representations.}$$

### 2.3 PEEL — `kill_up_n` is an S_n-equivariant interior operator

**The rule.** `D_n = {x ∈ PPF_{n+1} : x|_{[n]} ≠ ∅, Down_n(x) ≠ ∅}`. Define `kill_up_n(x) := {(a, b) ∈ x : b ≠ n}` — delete every relation pointing *into* `n` (i.e. erase `Up_n`). This is S_n-equivariant (`n` is fixed; the rule deletes a fixed relation-class). Its fixed set is exactly `A_n` (`Up_n(x) = ∅`).

> **Proposition 2.3 (PEEL, n-uniform).** *For every `n ≥ 3`, `kill_up_n : D_n → D_n` is a well-defined S_n-equivariant interior operator (monotone, `kill_up_n ≤ id`, idempotent) with fixed set `A_n`. Consequently `Δ(A_n) ↪ Δ(D_n)` is an S_n-equivariant homotopy equivalence, and `H̃_∗(Δ(D_n)) ≅ H̃_∗(Δ(A_n))` as S_n-representations.*

*Proof.* `kill_up_n` is a relation-set restriction, hence monotone and `≤ id`; it is idempotent (re-deleting `(·, n)` does nothing). Transitive closure is preserved: deleting all relations *into* `n` cannot destroy transitivity, because a composition `(a, n) · (n, b)` would force `(a, b)`, but `Up_n` and `Down_n` are never both non-empty for `x ∈ PPF_{n+1}` *if both were realised through* — more directly: any pair `(a, c)` derivable in `x` via `n` was `(a, n)·(n, c)`, and then `(a, c) ∈ x` already (transitivity of `x`); removing `(a, n)` leaves `(a, c)` intact. So `kill_up_n(x)` is a partial order. It has `x|_{[n]}` and `Down_n(x)` unchanged, both non-empty — so it lies in `D_n` *provided it is still proper*, i.e. non-total. **It is:** suppose `kill_up_n(x)` were total on `[n+1]`. Since `kill_up_n(x)` has `Up_n = ∅`, totality forces `Down_n = [n]` and `x|_{[n]}` total; but then `x ⊇ kill_up_n(x)` is also total on `[n+1]` (adding relations to a total order keeps it total/contradicts antisymmetry), so `x ∉ PPF_{n+1}` — contradicting `x ∈ D_n`. Hence `kill_up_n(x) ∈ D_n`. An interior operator on a poset induces a (here S_n-equivariant) homotopy equivalence between the order complex and that of its image (Björner, *Topological methods*, §10; the order-homotopy lemma for monotone `f ≤ id`). The image is the fixed set `A_n`. ∎

The harness confirms the interior-operator obligations directly at `n = 3` (`|D_3| = 96`, fixed set `|A_3| = 66`) and `n = 4` (`|D_4| = 2442`, fixed set `|A_4| = 1420`), and the structural argument at `n = 5`.

### 2.4 The reduction identity — n-uniform, S_n-equivariant, unconditional

Chaining §2.1–§2.3:

> **Theorem 2.4 (the n-uniform reduction identity).** *For every `n ≥ 3`, as S_n-representations,*
> $$\widetilde H_d(\Delta_{n+1}/\Delta_n)\;\cong\;2\cdot\widetilde H_{d-1}(\Delta(A_n))\qquad\text{for every degree }d,\ \text{unconditionally.}$$

Every step's hypothesis was proven for all `n ≥ 3` with no recourse to `Hyp`, `(UCC)`, or any per-n computation: MoveA by Prop. 2.1 (cones + Lemma L1), MoveB by Prop. 2.2 (Boolean cones), PEEL by Prop. 2.3 (one interior operator). The matchings underlying MoveA/MoveB are the cluster-lemma "toggle-apex" cone matchings whose apices are S_n-canonical (the new element of each fibre), and the patchwork theorem (Jonsson) assembles the fibrewise S_n-equivariant acyclic matchings into a global **S_n-equivariant acyclic cofiber matching `M_rel^{eq}`**; PEEL's interior operator is itself an S_n-equivariant discrete Morse collapse. So `M_rel^{eq}` is the S_n-equivariant n-uniform upgrade of M1's `M_rel` that the ticket asks for — *not* via "greedy + Forman" (which mg-6295 §8.2 records is *not* equivariant), but via the F14 order-ideal reduction recognised as an equivariant matching.

It remains to compute `H̃_∗(Δ(A_n))`.

---

## §3. Lemma L1 — the one load-bearing lemma

> **Lemma L1.** *Let `Q_0` be a total order (chain) on `[n]`, `n ≥ 3`. The poset*
> $$\overline L(Q_0) \;:=\; \{Q : \varnothing \ne Q \subsetneq Q_0,\ Q\ \text{transitively closed}\}$$
> *of nonempty proper sub-partial-orders of the chain (ordered by inclusion) has* **contractible** *order complex.*

*Proof.* Write the chain as `a_1 ≺ a_2 ≺ ⋯ ≺ a_n`, and set `r_\ast := (a_1, a_n)` — the single relation between the chain's bottom and top. `{r_\ast}` is transitively closed (one relation composes with nothing). Define

$$c(Q) \;:=\; \mathrm{tc}\bigl(Q \cup \{r_\ast\}\bigr),$$

the transitive closure. We claim `c` is a closure operator on `\overline L(Q_0)` whose image has a global minimum.

*`c` lands in `\overline L(Q_0)`.* `Q ∪ {r_\ast} ⊆ Q_0` and `Q_0` is transitively closed, so `c(Q) ⊆ Q_0`; and `c(Q) ⊇ {r_\ast} ≠ ∅`. The point is `c(Q) ≠ Q_0`. Computing the closure: from `r_\ast = (a_1, a_n)`, the only new transitive consequences use `(z, a_1) ∈ Q ⟹ (z, a_n)` (there are no relations *out of* `a_n`, the chain-top, in `Q ⊆ Q_0`). So

$$c(Q) \;=\; Q \;\cup\; \{r_\ast\} \;\cup\; \{(z, a_n) : (z, a_1) \in Q\}.$$

Every relation of `c(Q)` *into* `a_n` is therefore in `{r_\ast} ∪ {(z, a_n) : (z, a_1) ∈ Q}`; but `(z, a_1) ∈ Q ⊆ Q_0` forces `z ≺ a_1` in the chain, impossible for `z ≠ a_1`. Hence the *only* relation of `c(Q)` into `a_n` is `r_\ast = (a_1, a_n)`. For `n ≥ 3` the chain `Q_0` has the relation `(a_{n-1}, a_n)` with `a_{n-1} ≠ a_1`, which is therefore *not* in `c(Q)`. So `c(Q) ⊊ Q_0`, i.e. `c(Q) ∈ \overline L(Q_0)`.

*`c` is a closure operator.* Monotone: `Q ⊆ Q' ⟹ Q ∪ {r_\ast} ⊆ Q' ∪ {r_\ast} ⟹ \mathrm{tc}(\cdot) ⊆ \mathrm{tc}(\cdot)`. Extensive: `Q ⊆ c(Q)`. Idempotent: `r_\ast ∈ c(Q)`, so `c(c(Q)) = \mathrm{tc}(c(Q) ∪ \{r_\ast\}) = c(Q)`.

*The image has a global minimum.* `c(\overline L(Q_0)) = \{Q ∈ \overline L(Q_0) : r_\ast ∈ Q\}` — every element contains `r_\ast`, so `{r_\ast}` is the global minimum of the image (and `{r_\ast} ∈ \overline L(Q_0)`: it is nonempty, proper for `n ≥ 3`).

A poset with a global minimum has a contractible (cone) order complex. A closure operator `c` on a poset `P` induces a homotopy equivalence `Δ(P) ≃ Δ(c(P))` (Björner, *Topological methods*, §10.2; the order-homotopy lemma for monotone `f ≥ id`). Hence `Δ(\overline L(Q_0)) ≃ Δ(c(\overline L(Q_0)))`, a cone — contractible. ∎

**Remarks.** (a) The lemma is *purely combinatorial and fully n-uniform* — the closure operator `c` and the witness `r_\ast` are given by an n-independent formula. (b) It is the **single** topological input that is not "a cone" or "an interior operator": it is the one place a genuine homotopy-equivalence argument is needed, and it is reused twice — once in MoveA (Prop. 2.1) and once in the `A_n^t` attachment (§4.2). (c) The harness confirms it at `n = 3` (`|\overline L| = 5`, image-min `{(0,2)}`, direct reduced Betti `(0,0)`), `n = 4` (`|\overline L| = 38`, direct reduced Betti `(0,0,0,0,0)`), and `n = 5` (`|\overline L| = 355`, image-min `{(0,4)}`; the direct Betti is skipped — the order complex is too large to materialise — but the closure-operator proof *is* the n-uniform argument and needs no computation).

---

## §4. The terminal complex: `Δ(A_n) ≃_{S_n} Δ_n`

We compute `H̃_∗(Δ(A_n))` via the ideal/filter decomposition `A_n = A_n^{nt} ⊔ A_n^t` of §1.2.

### 4.1 `A_n^{nt}` retracts S_n-equivariantly onto `PPF_n`

> **Proposition 4.1.** *For every `n ≥ 3`, the map `c(Q, F) := (Q, [n])` is an S_n-equivariant closure operator on `A_n^{nt}`, and `c(A_n^{nt}) ≅ PPF_n` as S_n-posets. Hence*
> $$\Delta(A_n^{nt}) \;\simeq_{S_n}\; \Delta(PPF_n) \;=\; \Delta_n.$$

*Proof.* **Well-defined.** For `(Q, F) ∈ A_n^{nt}` (`Q` non-total): `[n]` is a filter of any `Q`, nonempty; and `¬([n] = [n] ∧ Q\ total)` holds because `Q` is non-total. So `(Q, [n]) ∈ A_n`, and `Q` non-total puts it in `A_n^{nt}`. **Closure operator.** Extensive: `F ⊆ [n]`, so `(Q, F) ≤ (Q, [n])`. Idempotent: `c(Q, [n]) = (Q, [n])`. Monotone: `(Q, F) ≤ (Q', F') ⟹ Q ⊆ Q' ⟹ (Q, [n]) ≤ (Q', [n])`. **Image.** `c(A_n^{nt}) = {(Q, [n]) : Q\ \text{nonempty non-total partial order on}\ [n]\}`; the assignment `(Q, [n]) ↦ Q` is a poset isomorphism onto `{Q : ∅ ≠ Q\ \text{non-total}\} = PPF_n` (`(Q,[n]) ≤ (Q',[n]) ⟺ Q ⊆ Q'`). **Equivariance.** `g ∈ S_n` fixes `[n]` setwise, so `c(g·(Q, F)) = c(g·Q, g·F) = (g·Q, [n]) = g·(Q, [n]) = g·c(Q, F)`. A closure operator that commutes with the group action induces an S_n-equivariant homotopy equivalence `Δ(A_n^{nt}) ≃_{S_n} Δ(c(A_n^{nt}))` (the order-homotopy retraction is natural, hence equivariant). ∎

The harness confirms all four obligations at `n = 3, 4, 5`, with `c(A_n^{nt})` equal as a set to `PPF_n` (`|img| = 12, 194, 4110`) and `c` commuting with the full `S_n`-action.

### 4.2 `A_n^t` attaches along contractible down-sets

> **Proposition 4.2.** *For every `n ≥ 3` and every `y ∈ A_n^t`, the open down-set `(A_n)_{<y} := \{z ∈ A_n : z < y\}` has* **contractible** *order complex. Consequently the S_n-equivariant order-ideal inclusion `Δ(A_n^{nt}) ↪ Δ(A_n)` is a homotopy equivalence.*

*Proof of the second sentence from the first.* Enumerate `A_n^t = \{y_1, y_2, …\}` in a linear extension and set `P_i := A_n^{nt} ∪ \{y_1, …, y_i\}` (each an order ideal of `A_n`). Then `Δ(P_i) = Δ(P_{i-1}) ∪ \mathrm{Cone}\bigl(Δ((P_i)_{<y_i})\bigr)`, glued along `Δ((P_i)_{<y_i}) = Δ((A_n)_{<y_i})` (all elements `< y_i` lie in `P_{i-1}`). If `Δ((A_n)_{<y_i})` is contractible, the pushout of a homotopy equivalence (`Δ((A_n)_{<y_i}) ↪ \mathrm{Cone}`) along a cofibration is a homotopy equivalence, so `Δ(P_{i-1}) ↪ Δ(P_i)`; composing, `Δ(A_n^{nt}) ↪ Δ(A_n)`. The inclusion is S_n-equivariant (`A_n^{nt}` is an S_n-invariant ideal, Lemma 1.2).

*Proof of the first sentence.* Fix `y = (Q_0, F_0) ∈ A_n^t`: `Q_0` a chain on `[n]`, `F_0` a nonempty proper filter `F_k` (top `k` of the chain), `1 ≤ k ≤ n−1`. Note properness is automatic on `(A_n)_{<y}`: every `(Q, F) < y` has `F ⊆ F_0 ⊊ [n]`, so `F ≠ [n]`. Split

$$(A_n)_{<y} \;=\; D \;⊔\; T,\qquad D := \{(Q, F) < y : Q \subsetneq Q_0\}\ \ (\text{ideal}),\qquad T := \{(Q_0, F) : \varnothing \ne F \subsetneq F_0\}\ \ (\text{filter}).$$

*The ideal `D`.* On `D`, `c_D(Q, F) := (Q, F_0)` is a closure operator: `F_0` is a filter of `Q_0`, hence of any `Q ⊆ Q_0`; `(Q, F_0) ∈ A_n` (proper, since `F_0 ⊊ [n]`); `(Q, F_0) < y` since `Q ⊊ Q_0`; extensive (`F ⊆ F_0`), idempotent, monotone — all immediate. Its image is `\{(Q, F_0) : ∅ ≠ Q ⊊ Q_0\} ≅ \overline L(Q_0)`, which is **contractible by Lemma L1**. So `Δ(D)` is contractible.

*The filter `T`.* The filters of the chain `Q_0` contained in `F_0` are the nested `F_1 ⊊ ⋯ ⊊ F_{k-1}`, so `T` is itself a *chain* of length `k−1` — `Δ(T)` is a simplex (or empty, when `k = 1`).

*Attaching `T` to `D` — induction on `k = |F_0|`.* For `t = (Q_0, F) ∈ T` (`F = F_j`, `j < k`), the down-set within `(A_n)_{<y}` is `((A_n)_{<y})_{<t} = (A_n)_{<t}` — the *full* down-set of `t` in `A_n`, since `t < y` already bounds everything below `t` by `y`. And `t ∈ A_n^t` with filter index `j < k`. By induction on `k`, `Δ((A_n)_{<t})` is contractible. (Base `k = 1`: `T = ∅`, so `(A_n)_{<y} = D` and we are done by Lemma L1.) Inductive step `k ≥ 2`: every `t ∈ T` attaches along a contractible down-set, so by the gluing argument above `Δ(D) ↪ Δ((A_n)_{<y})` is a homotopy equivalence; and `Δ(D)` is contractible. Hence `Δ((A_n)_{<y})` is contractible. ∎

The harness verifies the *structural ingredients* (the `c_D` closure operator landing on `\overline L(Q_0)`; `T` a chain; `((A_n)_{<y})_{<t} = (A_n)_{<t}`) at `n = 3, 4, 5`, and additionally recomputes `Δ((A_n)_{<y})` *directly* as contractible at `n = 3, 4` as a trip-wire (sizes up to `|(A_4)_{<y}| = 190`); at `n = 5` the down-sets `|(A_5)_{<y}|` reach `3004` and the direct order complex is not materialised — the structural proof is the n-uniform argument.

### 4.3 `H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)` as S_n-representations

> **Theorem 4.3.** *For every `n ≥ 3`,*
> $$\widetilde H_\ast(\Delta(A_n)) \;\cong\; \widetilde H_\ast(\Delta_n)\qquad\text{as }S_n\text{-representations, unconditionally.}$$

*Proof.* Prop. 4.2 gives an S_n-equivariant map `Δ(A_n^{nt}) ↪ Δ(A_n)` inducing an isomorphism on homology; since the map is S_n-equivariant, the induced homology isomorphism is an isomorphism *of S_n-representations*. Prop. 4.1 gives an S_n-equivariant homotopy equivalence `Δ(A_n^{nt}) ≃_{S_n} Δ(PPF_n) = Δ_n`, hence an S_n-equivariant homology isomorphism `H̃_∗(Δ(A_n^{nt})) ≅ H̃_∗(Δ_n)`. Compose. ∎

(One could upgrade Prop. 4.2 to an *equivariant* homotopy equivalence by attaching the elements of `A_n^t` orbit-by-orbit with the naturally-equivariant contractions of §4.2; but the homology-level statement of Thm. 4.3 is exactly what (UCC.1) requires, and we keep the argument at that level.)

The harness confirms Thm. 4.3 *directly* at `n = 3`: `H̃_∗(Δ(A_3)) = (0, 1, 0, 0)` and `H̃_∗(Δ_3) = (0, 1)` agree, both with equivariant Euler characteristic `sgn_{S_3}`. At `n = 4`: `H̃_∗(Δ_4) = (0, 0, 1, 0, 0)` with equivariant type `sgn_{S_4}` is recomputed directly, and `H̃_∗(Δ(A_4)) = (0, 0, 1) = sgn_{S_4}` is the F14 GREEN-cofiber-perfect result (the `1.5×10^7`-cell `Δ(A_4)` is not recomputed; the structural lemmas give the equality, F14's direct computation is the cross-check). At `n = 5` the equality is the structural conclusion — `Δ(A_5)` and `Δ_5` are both far too large to materialise, and that is the entire point: the proof is n-uniform.

---

## §5. The payoff — (UCC.1) ⟺ Hyp(n)

> **Theorem 5.1 (the F17 reduction of (UCC.1)).** *For every `n ≥ 3`, as S_n-representations,*
> $$\widetilde H_d(\Delta_{n+1}/\Delta_n) \;\cong\; 2\cdot\widetilde H_{d-1}(\Delta_n)\qquad\text{for every }d,\ \text{unconditionally.}$$
> *Consequently `(UCC.1)` at level `n` is* **equivalent** *to `Hyp(n)`:*
> $$\widetilde H^k(\Delta_{n+1}/\Delta_n) = \begin{cases} 2\cdot\mathrm{sgn}_{S_n} & k = n-1\\ 0 & k \ne n-1\end{cases}\qquad\Longleftrightarrow\qquad \widetilde H^k(\Delta_n) = \begin{cases}\mathrm{sgn}_{S_n} & k = n-2\\ 0 & k \ne n-2.\end{cases}$$

*Proof.* Combine Theorem 2.4 (`H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ(A_n))`) with Theorem 4.3 (`H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)`), both S_n-equivariant and unconditional. For the equivalence: over `ℚ`, `H̃^k ≅ (H̃_k)^\ast` as S_n-representations, and the representations in play are sums of the self-dual `sgn`, so cohomology and homology agree as S_n-representations; `Hyp(n)` says `H̃_{n-2}(Δ_n) = sgn_{S_n}` and `H̃_k(Δ_n) = 0` otherwise, which by the identity is `H̃_{n-1}(Δ_{n+1}/Δ_n) = 2·sgn_{S_n}` and `H̃_k = 0` otherwise — exactly `(UCC.1)`. The converse reads the identity backwards: `(UCC.1)` forces `2·H̃_{d-1}(Δ_n)` concentrated and `= 2·sgn` in degree `d = n−1`, hence `H̃_{n-2}(Δ_n) = sgn` and `H̃_k(Δ_n) = 0` else — `Hyp(n)`. ∎

**This is the F17 deliverable.** (UCC.1) is no longer a free-standing conditional hypothesis sitting outside the induction: it is *literally the inductive hypothesis Hyp(n)*, transported through an unconditional, n-uniform, S_n-equivariant reduction. The F10 cohomological-core induction (F10 §6.2–§6.3) is `Hyp(n) ⇒ Hyp(n+1)`, with the inductive step consuming `(UCC.1)` at level `n` (to supply `(\star)`) and `(UCC.2)` at level `n` (to supply `δ_n` injective). F17 supplies `(UCC.1)` at level `n` *from* `Hyp(n)` — i.e. for free. The induction becomes:

$$\mathrm{Hyp}(n)\ \xrightarrow[\text{(Thm. 5.1)}]{\text{F17 equivariant cofiber Morse}}\ (\mathrm{UCC.1})\ \text{at}\ n\ \xrightarrow[\text{F10 §6.2}]{+\ (\mathrm{UCC.2})\ \text{at}\ n}\ \mathrm{Hyp}(n+1).$$

**The only remaining conditional input of the F10 cohomological core is (UCC.2).**

---

## §6. The three F17 sub-questions, answered

The ticket poses three sub-questions. All three close.

### 6.1 Equivariance, n-uniformly — **YES**

*"Can M1's cofiber matching `M_rel` be constructed S_n-equivariantly, by an n-independent rule? Is F14's n = 4 reduction an instance of an n-uniform equivariant construction, or n = 4-specific?"*

**It is an instance of an n-uniform equivariant construction.** The F14 reduction MoveA/MoveB/PEEL is defined by an *n-independent rule* whose every ingredient is S_n-canonical: peel **element `n`** (which `S_n` fixes); split off the **Type-∅ ideal** `S = S_\downarrow ⊔ S_\uparrow` (S_n-invariant, the two components exchanged by the S_n-equivariant order-reversal); peel via **`kill_up_n`** (deletes the S_n-fixed relation-class `(·, n)`). §2 proves the collapse hypotheses hold for *every* `n ≥ 3` by n-independent arguments (Prop. 2.1–2.3). The cluster lemma / patchwork theorem assembles the fibrewise toggle-apex cone matchings — whose apices are the S_n-canonical fibre-defining elements — into a global **S_n-equivariant acyclic cofiber matching `M_rel^{eq}`** (Thm. 2.4). This is *not* M1's "greedy + Forman" matching (mg-6295 §8.2 explicitly: that one is *not* S_n-equivariant); it is the F14 order-ideal reduction *recognised as* an S_n-equivariant discrete Morse matching with the same critical cells.

### 6.2 Perfection, n-uniformly — **YES (⟺ Hyp(n))**

*"F10 §3.3 flagged perfection of `M_rel` as n-dependent and open beyond n = 3 → 4. Is there an n-uniform argument that the equivariant `M_rel` is perfect for all n?"*

**Yes — and the n-uniform argument identifies perfection at level `n` with `Hyp(n)`.** The reduction `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ(A_n))` is unconditional (Thm. 2.4), and `Δ(A_n) ≃_{S_n} Δ_n` (Thm. 4.3). So the critical-cell count of `M_rel^{eq}` equals `2·dim H̃_∗(Δ_n)` in each degree (shifted by 1). `M_rel^{eq}` is **perfect with critical vector `(0,…,0,2,0)`** — i.e. concentrated in degree `n−1` with `crit_{n-1} = 2` — **if and only if** `Δ_n` has reduced homology concentrated in degree `n−2` and `1`-dimensional, which is **exactly `Hyp(n)`**. F10 §3.3 was right that perfection is *not* n-independent *in isolation*; F17's contribution is to show perfection at level `n` is *precisely the inductive hypothesis*, hence discharged by the F10 induction rather than separately assumed. The "availability of unique gradient V-paths" worry (mg-6295 §6.3) is bypassed entirely: the equivariant reduction *is* the perfect matching whenever `Hyp(n)` holds, with no Forman-cancellation search.

### 6.3 Representation type, n-uniformly — **YES (⟺ Hyp(n))**

*"Given an n-uniform equivariant perfect `M_rel`, do its 2 critical `(n−1)`-cells carry `2·sgn_{S_n}` for all n? Is there an n-uniform character argument?"*

**Yes.** Theorem 4.3 is an isomorphism *of S_n-representations*: `H̃_{n-2}(Δ(A_n)) ≅ H̃_{n-2}(Δ_n)`. Under `Hyp(n)`, `H̃^{n-2}(Δ_n) = sgn_{S_n}`, so `H̃_{n-2}(Δ(A_n)) = sgn_{S_n}`, and by Thm. 2.4 the cofiber's degree-`(n−1)` cohomology is `2·sgn_{S_n}` — the 2 critical `(n−1)`-cells of `M_rel^{eq}` carry `2·sgn_{S_n}`. The "n-uniform character argument" the ticket asks for is *structural rather than character-theoretic*: it is the S_n-equivariance of the entire reduction (the closure operator of Prop. 4.1 commutes with `S_n`; the inclusion of Prop. 4.2 is S_n-equivariant; the `D_n ≅ U_n` duality of §2.2 is S_n-equivariant), which transports the *single* representation `H̃^{n-2}(Δ_n)` of `Hyp(n)` to the cofiber's `2·H̃^{n-2}(Δ_n)`. The mg-6295 (`n = 3`) and F14 (`n = 4`) datapoints are recovered as the small cases; the harness re-confirms `n = 3` directly (`H̃_∗(Δ(A_3)) = sgn_{S_3}`, equivariant Euler char) and `n = 4` via F14.

### 6.4 Net

All three sub-questions close. (UCC.1) — concentration half *and* representation-type half — is **proven for all `n`**, conditionally only on `Hyp(n)`, which the F10 induction supplies. The verdict is **GREEN-equivariant-uniform**.

---

## §7. What F17 establishes and does not establish

### 7.1 Establishes

- **Theorem 2.4** — the n-uniform, S_n-equivariant, **unconditional** reduction identity `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ(A_n))`. F14's MoveA/MoveB/PEEL reduction is an n-independent equivariant rule whose collapse hypotheses hold for all `n ≥ 3` (Prop. 2.1–2.3).
- **Lemma L1** — `{Q : ∅ ≠ Q ⊊ Q_0}` is contractible for any chain `Q_0` on `[n]`, `n ≥ 3`; proven by an explicit n-uniform closure operator. The single load-bearing topological lemma; reused in MoveA and the `A_n^t` attachment.
- **Theorem 4.3** — `H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)` as S_n-representations, **unconditionally**, for all `n ≥ 3`, via the S_n-equivariant closure operator `(Q, F) ↦ (Q, [n])` on `A_n^{nt}` (Prop. 4.1) and the contractible-down-set attachment of `A_n^t` (Prop. 4.2).
- **Theorem 5.1** — `(UCC.1)` at level `n` ⟺ `Hyp(n)`. (UCC.1) — both halves — is **proven for all `n`** modulo the F10 inductive hypothesis. It is removed from the list of independent conditional inputs of the F10 cohomological core.
- **All three F17 sub-questions** (equivariance / perfection / representation type, n-uniformly) close (§6).
- **Verification harness** — `scripts/compat_geom_F17_equivariant_morse.py`, 21 checks at `n = 3, 4, 5`, all pass: the `(Q, F)` model equals F14's `A_n` (exact set equality, `n = 3, 4`); Lemma L1; the MoveA/MoveB/PEEL hypotheses; the closure operator and attachment; and `H̃_∗(Δ(A_3)) = H̃_∗(Δ_3) = sgn`.

### 7.2 Does NOT establish

- **F17 does not prove `Hyp(n)` for general `n`.** It proves `(UCC.1) ⟺ Hyp(n)`; `Hyp(n)` itself is the F10 induction's conclusion, established by induction once `(UCC.2)` is supplied. F17 closes one of the two inductive-step inputs, not the induction.
- **F17 does not close (UCC.2).** See §7.3 — (UCC.2) is genuinely independent of the F17 mechanism. The ticket anticipated this (*"leaving only (UCC.2)"*).
- **F17 does not recompute `Δ(A_4)` or touch `Δ_5`/`Δ(A_5)` by direct computation.** The `n = 4` `Δ(A_4)` homology is cited from F14 (GREEN-cofiber-perfect); `n = 5` is structural-only. This is by design: the result is n-uniform, and the harness's role is to confirm the *hypotheses* of the n-uniform lemmas, not to recompute large complexes (cf. `feedback_focus_on_induction_not_special_cases`).
- **F17 does not touch route (iii) / mg-b345.** It stays parked, per the ticket. Option 3 closing GREEN means the route-(iii) escalation is *not* triggered (that escalation was conditioned on F17 *also* stalling — AMBER-option-3-stalls — which did not happen).
- **No new axioms; no Lean changes.** Pure structural equivariant-discrete-Morse / order-complex topology, plus a stdlib verification harness. The in-tree Lean 4-axiom trust surface is untouched.

### 7.3 The (UCC.2) interaction — why it is independent of the F17 mechanism

The F17 reduction computes the *cofiber* `Δ_{n+1}/Δ_n` — equivalently, it constructs the **cofiber matching `M_rel^{eq}`** alone. (UCC.2) is the statement that the connecting map `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` is injective. F10 §6.4 phrases (UCC.2) Morse-theoretically: it is the statement that the *cross-boundary* Forman cancellation reducing `crit(M_{n+1}) = crit(M_n) ⊔ crit(M_rel)` to a perfect `M_{n+1}` succeeds — i.e. it is about the **gluing** of `M_n` and `M_rel`, not about `M_rel` in isolation. F17 constructs `M_rel^{eq}` and proves it perfect with the right S_n-type, n-uniformly; it says nothing about how `M_n` and `M_rel^{eq}` interact across the `Δ_n / `relative boundary. So (UCC.2) is **independent** of the F17 mechanism — F17 neither needs it (Theorems 2.4, 4.3, 5.1 never invoke `δ_n`) nor produces it. This matches F16 §5's parallel finding that the route-(ii) presentation argument was independent of (UCC.2): both the dead route (ii) and the live route (option 3) leave (UCC.2) untouched, for the same structural reason — (UCC.2) is about the *absolute* tower's connecting maps, downstream of any single-pair cofiber computation.

The surviving handle for (UCC.2): the cofiber LES `H̃^{n-2}(Δ_{n+1}) \xrightarrow{ι_n^\ast} H̃^{n-2}(Δ_n) \xrightarrow{δ_n} H̃^{n-1}(Δ_{n+1}/Δ_n)` shows `δ_n` is injective iff `ι_n^\ast = 0` on `H̃^{n-2}`. Under `Hyp(n)` this is "the inherited `sgn`-class of `Δ_n` dies in `Δ_{n+1}`" — a statement about the absolute tower. F17 hands the (UCC.2) sub-problem a clean setting (the cofiber side is now completely understood, n-uniformly) but does not solve it. This is the recommended F18 target (§8.3).

---

## §8. Verdict, and the program after F17

### 8.1 Verdict: GREEN-equivariant-uniform

Per the F17 verdict matrix: **GREEN-equivariant-uniform** — *"'M_rel perfect + S_n-equivariant' established n-uniformly; (UCC.1) PROVEN for all n (both halves)."* All three sub-questions close: the F14 reduction is an n-uniform S_n-equivariant rule (§6.1), its perfection at level `n` is `Hyp(n)` (§6.2), and its 2 critical `(n−1)`-cells carry `2·sgn_{S_n}` under `Hyp(n)` (§6.3). This is the "MAJOR — with the F10 core, only (UCC.2) remains of (UCC)" branch.

It is not GREEN-partial (all three sub-questions close, not one or two). It is not AMBER-option-3-stalls (the equivariant M1 upgrade *did* go n-uniform — so the route-(iii) PM/Daniel escalation is *not* triggered). It is not RED-pivot-fails (F14's `n = 4` reduction was emphatically *not* `n = 4`-specific — it is the `n = 4` instance of Theorems 2.4 & 4.3, and the harness confirms the same construction at `n = 3, 5`).

### 8.2 What survives, what is closed

| | status after F17 |
|---|---|
| (UCC.1) **concentration** half (M1's "`M_rel` perfect") | **PROVEN for all `n`**, conditionally on `Hyp(n)` — i.e. discharged by the F10 induction (Thm. 5.1, §6.2). |
| (UCC.1) **representation-type** half (`B_n = 2·sgn_{S_n}`) | **PROVEN for all `n`**, conditionally on `Hyp(n)` (Thm. 5.1, §6.3). |
| (UCC.1) **as a whole** | **CLOSED** — both halves reduced, n-uniformly and S_n-equivariantly, to `Hyp(n)`. No longer an independent conditional input of the F10 core. |
| The "n-dependence of perfection" gap (F10 §3.3, mg-6295 §6.3) | **RESOLVED** — perfection at level `n` *is* `Hyp(n)`; there is no separate n-uniform perfection statement to prove. |
| F14's `n = 4` order-ideal reduction | **Not `n = 4`-specific** — it is the `n = 4` instance of an n-uniform S_n-equivariant construction (Theorems 2.4, 4.3). |
| Route (ii) | Remains **CLOSED-negative** (F16). F17 does not revisit it; option 3 *replaced* it. |
| Route (iii) / mg-b345 | Remains **PARKED**. The escalation trigger (F17 *also* stalling) did **not** fire. |
| **(UCC.2)** (`δ_n` injective for general `n`) | **The sole remaining conditional input** of the F10 cohomological core. Untouched by F17; independent of the F17 mechanism (§7.3). The recommended next target. |
| F10 cohomological core | **GREEN-conditional intact** — and the conditionality has narrowed from `{(UCC.1), (UCC.2)}` to `{(UCC.2)}` alone. |

### 8.3 Recommendation (a polecat recommendation, for the PM to weigh)

With F17, the F10 cohomological core's *single* open gap is **(UCC.2)**. The recommended next ticket is an **F18** targeting (UCC.2) directly: prove `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` injective n-uniformly, equivalently `ι_n^\ast = 0` on `H̃^{n-2}` (§7.3). F17 has made the *cofiber side* completely transparent — `H̃^{n-1}(Δ_{n+1}/Δ_n) = 2·H̃^{n-2}(Δ_n)` with the explicit reduction dictionary `Δ_{n+1}/Δ_n ⇝ 2·Δ(A_n) ≃ 2·Δ_n` — so (UCC.2) can now be attacked as a question purely about the absolute tower `(Δ_n)_n` and the inclusion `ι_n`. Route (iii) / mg-b345 should remain **parked** (its escalation condition — option 3 stalling — was not met). This keeps the program squarely on "finish the induction internally."

### 8.4 Trust-surface impact

**None.** F17 introduces no new axioms, makes no Lean changes, runs no HPC. It is structural equivariant-discrete-Morse / order-complex topology (Theorems 2.4, 4.3, 5.1; Lemma L1) building on M1 (mg-6295) and F14's equivariant reduction (mg-3839), plus a pure-Python stdlib verification harness (≈ 46 s, 21 checks, all pass). The in-tree Lean artifact `width3_one_third_two_thirds` (4-axiom trust surface) and the general-`n` paper-level track are untouched.

---

## §9. References

### 9.1 Predecessor and sibling mg-tickets

- **mg-f893** — F16 (route (ii) weaker form): **AMBER-route-ii-stalls.** `docs/compatibility-geometry-F16-central-stability-presentation.md`. §7.3 (**the option-3 pivot — F17's mandate**), §0.4 (what survives — (UCC.1) representation-type half "returns to option 3"), §4.3 (why route (ii) is circular), §5 (the (UCC.2) clarification — F17 §7.3 mirrors it for option 3). **Parent.**
- **mg-3839** — F14 (PCR-Lit-2′): **GREEN-cofiber-perfect.** `docs/compatibility-geometry-F14-pcr-lit2prime.md`, `scripts/compat_geom_cofiber_morse_n4n5.py`. §1 (the MoveA/MoveB/PEEL reduction — **the template F17 makes n-uniform**), §1.2 (the pipeline for `Δ_5/Δ_4`, the `2·Δ(A_4)` collapse), §2.2 (`B_4 = 2·sgn_{S_4}`, equivariant Euler char), §4.2 ("the reduction *mechanism* is itself n-uniform … but each level's collapse hypotheses are re-verified computationally, not assumed" — **the gap F17 closes**). **THE TEMPLATE.**
- **mg-8355** — F15 (E2): **AMBER-partial3-not-iso.** `docs/compatibility-geometry-F15-e2-partial-test.md`. §7.3 option 3 (where the pivot was first documented).
- **mg-ecf6** — F13 (E1): **GREEN-functoriality-established.** `docs/compatibility-geometry-F13-shift-aware-functoriality.md`. The good-pair / triple-LES conventions used in §1.
- **mg-b352** — F11: **GREEN-route-traction.** `docs/state-F11.md`. §3 (route (i) closed-negative), §4 (route (ii) survey), §5 (route (iii) parked "unless routes (i)+(ii) both stall").
- **mg-8216** — F10: general-`n` unified proof synthesis. **GREEN-conditional.** `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. §3 (Mechanism M1 — §3.2 the n-uniform acyclicity, **§3.3 perfection n-dependent and open beyond `n = 3→4` — RESOLVED by F17 §6.2**), §6.1 (`Hyp(n)`), §6.2 (the inductive step — consumes (UCC.1) + (UCC.2)), §6.3 (**(UCC)**), §6.4 (M1 → (UCC)).
- **mg-6295** — PCR-Lit-2 / M1: discrete Morse on the cofiber. `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`, `scripts/compat_geom_cofiber_morse_n3n4.py`. §3.2 (`M_rel` perfect at `n = 3→4`, critical vector `(0,0,2,0)`), §6 (the n-uniform extension mechanism — §6.1 the downward-closed-subcomplex lemma), §6.3 / §8.2 (perfection verified *only* at `n = 3→4`; "greedy + Forman matching is **not** S_3-equivariant" — **F17 supplies the equivariant matching by a different route**).
- **mg-b345** — F8″: route (iii), **PARKED** — F17 does not touch it; its escalation trigger did not fire (§8.2).

### 9.2 Mathematical literature

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998); *A user's guide to discrete Morse theory*, Sém. Lothar. Combin. 48 (2002) — discrete Morse theory; acyclic matchings; the Morse complex.
- P. Hersh, *On optimizing discrete Morse functions*, Adv. Appl. Math. 35 (2005) — the cluster lemma (fibrewise toggle-apex matchings assemble).
- J. Jonsson, *Simplicial complexes of graphs*, LNM 1928 (2008) — the patchwork theorem (fibrewise acyclic matchings assemble into a global acyclic matching).
- A. Björner, *Topological methods*, in *Handbook of Combinatorics* (1995), §10 — the order-homotopy lemma: a monotone `f : P → P` with `f ≥ id` (closure operator) or `f ≤ id` (interior operator) induces `Δ(P) ≃ Δ(f(P))`; the gluing lemma for attaching cones along contractible subcomplexes.
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11–13 — discrete Morse theory for subcomplex pairs; order-ideal filtrations; the closure/interior-operator collapses.
- D. Quillen, *Higher algebraic K-theory I*, LNM 341 (1973), §1 — Theorem A / the fibre lemma (the homotopy-colimit principle underlying the order-ideal filtration arguments).

### 9.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (F17 is pure internal structural mathematics; route (iii)/mg-b345 stays parked, its escalation trigger un-fired — §8.2.)
- 2026-05-14T08:05Z — focus on the induction, not special cases. (F17's content is *entirely* n-uniform: Theorems 2.4, 4.3, 5.1 and Lemma L1 are general-`n` statements with n-independent proofs. The `n = 3, 4, 5` harness checks the *hypotheses* of those n-uniform lemmas — it is a trip-wire, not a datapoint hunt; no new HPC, no new `n`-datapoints.)

---

*Polecat: mg-4d3a (F17). Branch: `compat-geom-F17-nuniform-equivariant-morse`. Verdict: **GREEN-equivariant-uniform** — the S_n-equivariant cofiber discrete Morse mechanism is n-uniform. F14's MoveA/MoveB/PEEL order-ideal reduction is an n-independent S_n-equivariant rule whose collapse hypotheses hold for all `n ≥ 3` (Lemma L1 + Boolean cones + an interior operator); its terminal complex satisfies `H̃_∗(Δ(A_n)) ≅ H̃_∗(Δ_n)` as S_n-representations (S_n-equivariant closure operator onto `PPF_n` + contractible-down-set attachment), unconditionally. Hence `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)` as S_n-reps for all `n ≥ 3`, unconditionally — so **(UCC.1) ⟺ Hyp(n)**, both halves, discharged by the F10 induction. All three sub-questions close; (UCC.1) PROVEN for all `n`; only (UCC.2) remains of (UCC). No new axioms; no Lean changes. Cumulative state: `docs/state-F17.md`.*
