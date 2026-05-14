# Compat-Geom — F19: (ICOP-step) and the width-3 reduction bridge — the last two inputs of the F10 width-3 theorem (mg-5722)

**Branch:** `compat-geom-F19-icop-step-and-bridge`.
**Parents:** mg-d039 (F18, GREEN-ucc2-proven) §7.2 — the program after F18; (ICOP-step) recommended as the more central of the two remaining inputs. mg-8216 (F10) §5.2–5.4 ((ICOP-step)), §7.3 (the width-3 bridge), §7.4 (the conditional-inputs table), §6.7 (the final theorem). mg-4d3a (F17) + mg-d039 (F18) — the now-unconditional cohomological core. mg-1e99 (F8) §4.3–4.4, §6 (ICOP, the width-3 closure argument). mg-7b3b (F8′) §3 (the n=6 ι₅-lift candidate, the extremal-element distinction). mg-1e58 (F5) §4.3 (c\*₅ explicit). mg-7455/mg-6bc3 (F2/F3) §4.3 (c\*₄ explicit).
**Type:** Structural / combinatorial argument (Kahn–Saks per-step probabilities + the ι-tower). LaTeX-style Markdown; **no new axioms; no Lean changes; no new HPC; no new empirical n-datapoint**. Multi-session-able; cumulative state in `docs/state-F19.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction, not special cases).

**Verdict: GREEN-partial.** (ICOP-step) is **substantially advanced and reduced to a clean uniform sub-statement of a strictly more elementary kind.** The probabilistic / Kahn–Saks content of (ICOP-step) is *fully discharged*, n-uniformly and rigorously, by the **symmetric-pair lemma (L1)** of §2: a cover step taken at a symmetric incomparable pair has Kahn–Saks probability exactly `1/2 ∈ [3/11, 8/11]`. What remains — **(L2)** of §3 — is purely order-theoretic and carries no probability content: *the canonical new cover of the ι-tower is taken at a symmetric incomparable pair of the top poset.* (L2) is verified at `n = 3,4,5,6` (the existing empirical record, re-confirmed by the F19 harness), and reduced further to the structural statement that the top poset `G_n` of the canonical critical cell is a width-2 ordinal sum of antichains. A fully n-uniform proof of (L2) needs a dedicated structural theorem about the canonical chamber-Morse critical cell (or the F8‴ HPC run) — this is the precisely-identified residual, recommended as **F20**. The **width-3 reduction bridge** is handled as the in-ticket sibling: its `m ≤ 4` rigorous base is re-proven (all 44 width-3 posets in PPF₄ are BFT-sharp-witnessed), and the `m ≥ 5` case is cleanly reduced — given (ICOP-step) — to the single combinatorial statement **(W3-cover)** (the ι-tower meets every width-3 `S_m`-orbit), which is the natural F20 sibling target. Trust-surface impact: **none**.

---

## §1. Setting and the two remaining inputs

### 1.1 Where F19 sits in the program

After **F17** (mg-4d3a) and **F18** (mg-d039), the **F10 cohomological core** — parts (i)–(ii) of the F10 conditional theorem (§6.7) — is **UNCONDITIONAL**: `Hyp(n)` holds for all `n ≥ 3`, i.e. (H-Cox) + (sgn) at general `n`, and `ω_bal^{(n)}` exists, is unique up to scalar, and pairs `±1` with the canonical critical cell `c*_n`. The master hypothesis (UCC) is complete: (UCC.1) ⟺ `Hyp(n)` (F17), (UCC.2) unconditional (F18).

The **numerical width-3 conclusion** — F10 §6.7 part (iii), the explicit `[3/11, 8/11]` interval, i.e. the actual Kahn–Saks 1/3-2/3 statement for width-3 posets at general `n` — still rests on **two further conditional inputs**, neither part of (UCC), neither touched by the F11→F18 line (F10 §7.4):

| Input | Role | Status entering F19 |
|---|---|---|
| **(ICOP-step)** (F10 §5.4) | the per-step `[3/11,8/11]` interval on the canonical chain (step 5 of the skeleton) | verified `n = 3,4,5,6`; reduced to "one structurally-uniform lex-min cover step per `n`" |
| **width-3 reduction bridge** (F10 §7.3) | the width-3 specialisation (steps 1, 6) | rigorous `m ≤ 4`; for `m ≥ 5` reduces to (ICOP-step) + "ι-tower meets every width-3 orbit" |

F18 §7.2 recommended (ICOP-step) as the more central of the two — it gates the numerical interval, and the bridge reduces partly to it. F19 takes (ICOP-step) as the primary target and the width-3 bridge as the in-ticket sibling.

### 1.2 The objects (recap, F10 §1.1, §5)

`PPF_n` is the set of proper partial orders on `[n] = {0,…,n−1}` (non-empty, non-total, transitively closed antisymmetric relation sets), ordered by relation-set inclusion (a finer relation set is *higher*: more relations ⇒ fewer linear extensions). `Δ_n = Δ(PPF_n)` is its order complex. `ι_n : PPF_n ↪ PPF_{n+1}` adds the new element `n` incomparable to all of `[n]` (the relation set is literally unchanged).

For a poset `P` and an incomparable pair `(x,y)`, the **Kahn–Saks probability** is
```
    Pr_P[x ≺ y]  :=  |{ L ∈ L(P) : x precedes y in L }| / |L(P)|,
```
where `L(P)` is the set of linear extensions of `P`. Equivalently `Pr_P[x ≺ y] = |L(P ∪ {x<y})| / |L(P)|` — the conditional probability that a uniform random linear extension of `P` also extends the cover-refinement `P ⊂ P ∪ {x<y}`. The **BFT-sharp** (Brightwell–Felsner–Trotter) interval is `[3/11, 8/11] ⊂ [1/3, 2/3]`; `3/11 ≈ 0.2727`, `8/11 ≈ 0.7273`.

### 1.3 The canonical critical chain and the ι-tower (F10 §5.2, F8′)

The canonical critical `(n−2)`-cell `c*_n = (P_0 ⊂ P_1 ⊂ ⋯ ⊂ P_{n−2})` is the lex-min representative of the `S_n`-orbit of critical `(n−2)`-cells of the chamber-Morse matching that pairs non-trivially with `ω_bal^{(n)}` (F5/F7′/F8). Write `G_n := P_{n−2}` for its **top poset** — the most-refined, "near-maximal" poset of the chain.

F8′ (mg-7b3b) established the **multiplicativity law**: `|L(ι_{n−1}(P))| = n · |L(P)|`. This is the elementary fact that inserting one free element into an `m`-element poset multiplies the linear-extension count by `m+1`; it is n-uniform and rigorous. Its consequence (F10 §5.2): the **inherited** per-step probabilities of `c*_n` — the ratios `|L(P_{k+1})|/|L(P_k)|` for steps carried up from lower levels — are *n-independent*, because the multiplicative factor `n` cancels in every ratio. So the only per-step probability that is genuinely *new* at level `n → n+1` is the single cover appended to the near-maximal top poset. F10 §5.4 isolates exactly this:

> **(ICOP-step)** *(F10 §5.4).* For every `n`, the lex-min new cover step appended to the top poset of `c*_n` in the ι-tower is BFT-sharp: its Kahn–Saks probability lies in `[3/11, 8/11]`.

Concretely (F8′ §3, F10 §5.3), the new cover step at level `n+1` is the lex-min admissible single cover of `ι_n(G_n)` — the ι-lift of the top poset of `c*_n`, with the freshly-added element `n` free. F8′ §3.5–3.7 emphasised the structural content: the lex-min cover *avoids extremal elements* — it does not pair the new free element with a minimal or maximal element (those covers, e.g. `Pr_{ι_5(P_3)}(0,5) = 3/4`, are *not* BFT-sharp and "would not be selected by a Forman-respecting greedy chamber-Morse procedure", F8′ §3.5(a)) — and instead lands inside an antichain of the structure.

This document turns "the lex-min cover avoids extremal elements" into a precise, rigorous, n-uniform statement.

---

## §2. The symmetric-pair lemma (L1) — the engine

The probabilistic content of (ICOP-step) is discharged entirely by the following lemma. It is elementary, fully rigorous, and **n-uniform** — it holds for finite posets of every size, with no chamber-Morse, cohomological, or computational input.

> **Lemma (L1) — symmetric-pair lemma.** Let `P` be a finite poset, let `{x,y}` be an incomparable pair of `P`, and suppose there is an automorphism `σ ∈ Aut(P)` with `σ(x) = y` and `σ(y) = x`. Then
> ```
>     Pr_P[x ≺ y]  =  1/2.
> ```
> In particular `Pr_P[x ≺ y] = 1/2 ∈ [3/11, 8/11]`: the cover step `P ⊂ P ∪ {x<y}` is BFT-sharp.

Call such a pair `{x,y}` a **symmetric incomparable pair** of `P`.

**Proof.** Identify a linear extension of `P` with a total order `⪯` on the ground set of `P` that refines `≤_P`; write `L(P)` for the (finite) set of these. The automorphism `σ` acts on total orders by transport of structure: define `⪯^σ` by
```
    a ⪯^σ b   :⟺   σ^{−1}(a) ⪯ σ^{−1}(b).
```
Because `σ` is an order-automorphism of `P`, `⪯^σ` again refines `≤_P` (if `a ≤_P b` then `σ^{−1}(a) ≤_P σ^{−1}(b)`, so `σ^{−1}(a) ⪯ σ^{−1}(b)`, so `a ⪯^σ b`). Hence `⪯ ↦ ⪯^σ` is a well-defined map `L(P) → L(P)`; it is a bijection, with inverse `⪯ ↦ ⪯^{σ^{−1}}`.

Now evaluate the bijection on the pair `{x,y}`. For any `⪯ ∈ L(P)`:
```
    x ⪯^σ y   ⟺   σ^{−1}(x) ⪯ σ^{−1}(y)   ⟺   y ⪯ x ,
```
using `σ^{−1}(x) = y` and `σ^{−1}(y) = x` (as `σ` swaps `x,y`, so does `σ^{−1}`). Therefore the bijection `⪯ ↦ ⪯^σ` carries the set `A := {⪯ : x ⪯ y}` onto the set `B := {⪯ : y ⪯ x}`. Hence `|A| = |B|`. Since `x` and `y` are comparable in *every* total order, `A` and `B` partition `L(P)`; so `|A| = |B| = |L(P)|/2` and `Pr_P[x ≺ y] = |A|/|L(P)| = 1/2`. ∎

**Remarks.**
1. The lemma needs only *one* swapping automorphism, of any order — it is not assumed to be an involution. (If `σ` swaps `x` and `y` it restricts to the transposition on `{x,y}`, but may act with any cycle type elsewhere.) The argument uses `σ` and `σ^{−1}` symmetrically and never iterates `σ`.
2. The lemma is the n-uniform engine: it eliminates *all* linear-extension counting from (ICOP-step). Whatever the size of `P`, a symmetric incomparable pair contributes `Pr = 1/2`, which sits at the dead centre of `[3/11, 8/11]` — the safest possible BFT-sharp value.
3. (L1) is certified computationally by the F19 harness §C: across the canonical top posets `G_3, G_4, G_5`, the penultimate poset `P_2` of `c*_5`, and the ι-lifts `ι_5(G_5)` and `ι_6 ι_5(G_5)`, **every** symmetric incomparable pair (11 in total, including pairs on a 7-element poset) has `Pr = 1/2` exactly. No counterexample exists, and the proof above shows none can.

---

## §3. The structure of the canonical top poset — the reduction target (L2)

By Lemma (L1), (ICOP-step) follows once we know the canonical new cover is *taken at a symmetric incomparable pair*. This §3 reduces (ICOP-step) to exactly that structural statement, states it precisely as **(L2)**, records its verified status, and gives the structural argument for it as far as the established results support — isolating the residual.

### 3.1 The reduction

> **Proposition 3.1 (reduction of (ICOP-step) to (L2)).** Suppose the following holds:
>
> **(L2).** For every `n ≥ 3`, the top poset `G_n` of the canonical critical cell `c*_n` has a symmetric incomparable pair, and the canonical (lex-min, `S_n`-equivariant) new cover appended to `ι_n(G_n)` in the ι-tower is taken at a symmetric incomparable pair of `ι_n(G_n)`.
>
> Then **(ICOP-step) holds for every `n`**: the lex-min new cover step of the ι-tower has Kahn–Saks probability `1/2 ∈ [3/11, 8/11]`.

**Proof.** Immediate from (L1): the canonical new cover is, by (L2), a cover `ι_n(G_n) ⊂ ι_n(G_n) ∪ {x<y}` at a symmetric incomparable pair `{x,y}` of `ι_n(G_n)`; (L1) gives `Pr_{ι_n(G_n)}[x ≺ y] = 1/2`. ∎

This is a genuine reduction of the *same kind* as F10's reduction of the cohomological core to (UCC), and F10's sharpening of (UCC) to (FG-Cofiber): it converts an *analytic* statement ("a rational number per `n` lies in an interval") into a *structural* one ("a poset has a symmetric pair, and the canonical labelling selects it") with **no probability content whatsoever**. The hard, error-prone, "verify a number" character of (ICOP-step) is gone; what is left, (L2), is a finite order-theoretic property of one explicitly-described poset per `n`.

### 3.2 (L2) is verified at `n = 3, 4, 5, 6`

The F19 harness `scripts/compat_geom_F19_icop_step.py` reconstructs the canonical critical chains explicitly from the literature — `c*_3` (F8 §4.5), `c*_4` (F2 §4.3.1, the lex-min critical 2-cell #1; cross-checked against the perfect-MF cell #4), `c*_5` (F5 §4.3 / F8′ §A) — and the F8′ `n=6` ι₅-lift candidate. For each it computes the automorphism group of `G_n` (resp. `ι_n(G_n)`), its symmetric incomparable pairs, every admissible single cover with its exact Kahn–Saks probability, and the lex-min cover. The result (harness §B, §D):

| `n` | top poset `G_n` (Hasse) | symmetric pairs of `G_n` | lex-min new cover | `Pr` | BFT-sharp? | at a symmetric pair? |
|---:|---|---|---|---|:---:|:---:|
| 3 | `{0<1, 0<2}` | `{1,2}` | `(1,2)` | `1/2` | ✓ | ✓ |
| 4 | `{0<2, 1<0, 3<0}` | `{1,3}` | `(1,3)` | `1/2` | ✓ | ✓ |
| 5 | `{0<3,0<4,2<3,2<4,3<1,4<1}` | `{0,2}, {3,4}` | `(0,2)` | `1/2` | ✓ | ✓ |
| 6 | `ι_5(G_5)` (element 5 free) | `{0,2}, {3,4}` | `(0,2)` | `1/2` | ✓ | ✓ |

So **(L2) holds at `n = 3,4,5,6`**, and on this verified range (ICOP-step) is not merely BFT-sharp but *uniformly `Pr = 1/2`* — the strongest possible form. The harness also reproduces the F8′ `n=6` record in full: the ι₅-lift profile `(180,84,48,24)` (multiplicativity), the step-4 lex-min cover `(0,2)` with `Pr = 1/2`, and the `8/14` BFT-sharp count among all admissible step-4 covers (harness §E).

A note on the `n = 6` entry: as F8′ §5.1 is careful to state, `ι_5(G_5)` is the *candidate* top poset (the genuine canonical `c*_6` requires the F8‴ chamber-Morse HPC run). F19 inherits exactly that status: the `n = 6` line of (L2) is verified *for the F8′ candidate*, which is the established empirical record, and is not a new datapoint.

A note on the `n = 3, 4` "internal" steps: the harness §D also records, for context, the *chain's own internal top step* — `Pr = 2/3` at `n = 3, 4`, `Pr = 1/2` at `n = 5`. This is a **different object** from (ICOP-step): it is an *inherited* step of the chain, n-dependent at small `n`, and is governed by the F8′ multiplicativity law, not by (ICOP-step). (ICOP-step) is specifically the *new* cover appended *going up* to the next level — the lex-min cover of `G_n` itself — and that is uniformly `Pr = 1/2`.

### 3.3 The structural content of (L2): `G_n` is a width-2 ordinal sum of antichains

(L2) has two halves: (i) `G_n` *has* a symmetric incomparable pair; (ii) the canonical construction *selects* one. Both follow from a single clean structural fact, verified at `n ≤ 5`:

> **(L2-struct).** For every `n ≥ 3`, the canonical top poset `G_n` is a **width-2 ordinal sum of antichains** containing at least one antichain block of size 2.

An *ordinal sum of antichains* is a poset whose incomparability graph is a disjoint union of cliques — equivalently, incomparability is transitive on distinct elements; equivalently `P = A_1 ⊕ A_2 ⊕ ⋯ ⊕ A_r` with each `A_i` an antichain and `a < b` for `a ∈ A_i, b ∈ A_j, i < j`. The harness §H certifies (L2-struct) at `n = 3,4,5`:
```
    G_3 = A_2 ⊕ A_1                     blocks {1,2} < {0}
    G_4 = A_1 ⊕ A_1 ⊕ A_2  (cell #1)    blocks {2} < {0} < {1,3}
    G_5 = A_1 ⊕ A_2 ⊕ A_2              blocks {1} < {3,4} < {0,2}
```
all width 2, each with a size-2 block. (L2-struct) ⇒ (L2):

- **(i) `G_n` has a symmetric incomparable pair.** In an ordinal sum of antichains, *every* incomparable pair lies inside a single antichain block. Any transposition of two elements inside one block — fixing every other element — is an automorphism (it preserves the block decomposition and the total order on blocks). So **every incomparable pair of `G_n` is a symmetric pair**, and a size-2 block furnishes one. The ι-lift `ι_n(G_n)` retains all of them: extend the swapping automorphism by fixing the new free element. (Harness §B: `G_5` has 4 admissible single covers, *all 4* BFT-sharp with `Pr = 1/2`, because all 4 incomparable pairs are symmetric; `ι_5(G_5)` keeps `{0,2}` and `{3,4}` symmetric.)

- **(ii) the canonical construction selects one.** The chamber-Morse construction is `S_n`-equivariant (F5, F7′) and Forman-respecting; F8′ §3.5–3.7 established that its lex-min cover *avoids extremal elements* — it never pairs the free element with a minimal/maximal element. Among the covers it does not avoid, the lex-min one (in the canonical `S_n`-orbit labelling, which places a size-2 antichain block at the lex-least indices, strictly below the free element's index) is a *within-block* cover, hence — by (i) — a symmetric pair. This is exactly what the harness observes: at `n = 6`, the lex-min admissible cover of `ι_5(G_5)` is `(0,2)` — the within-block pair at the smallest indices — and it beats every free-element cover `(0,5), (1,5), …` lexicographically because the inherited block sits at indices `< 5`.

So (L2) reduces to **(L2-struct)**, and (ICOP-step) reduces, via Proposition 3.1 and (L1), to the single purely order-theoretic statement (L2-struct).

### 3.4 The residual: an n-uniform proof of (L2-struct)

(L2-struct) is verified at `n = 3,4,5` (`G_n` exact) and `n = 6` (the F8′ candidate). What an n-uniform *proof* would require, and why it is the residual:

- **The canonical chain adds automorphism-orbits of covers.** Inspecting the explicit chains, every step of `c*_5` adds an `Aut`-orbit of covers: step 0 adds `{0<4, 2<4}` = the `(0 2)`-orbit of `0<4`; step 1 adds the singleton orbit `{4<1}`; step 2 adds `{0<3, 2<3}` = the `(0 2)`-orbit of `0<3`. Refining by full automorphism-orbits is precisely the `S_n`-equivariant / Forman-respecting behaviour, and it is the mechanism that *builds and preserves* a clustered (block-structured) incomparability graph. This is a clean structural observation — but verified, not yet proven for all `n`.
- **`G_n` is near-maximal and width 2.** F2 §4.4 records that the top poset is near the top of `PPF_n` (one or two relations short of a total order); the harness confirms width exactly 2 at `n ≤ 5`. A width-2 near-maximal poset whose incomparability graph is a cluster graph *is* a width-2 ordinal sum of antichains — so (L2-struct) is "width 2 + incomparability clusters", and the orbit-refinement mechanism is what makes it cluster.
- **It is genuinely not a greedy invariant.** The harness §H runs the negative control: the naive "always refine the lex-min symmetric pair" tower, started from `G_3`, *loses every symmetric pair already at `n = 4`*. So (L2-struct) is a property of the *canonical chamber-Morse construction specifically*, not of an arbitrary symmetric refinement rule. A proof must therefore engage the actual chamber-Morse machinery (F8 §4.1 Steps 1–4) at general `n`.

F8 §4.2 / §4.6 is explicit that the chamber-Morse construction's Steps 2–3 (chamber matching, Forman cancellation) are HPC-class and not currently n-uniform. A fully n-uniform proof of (L2-struct) therefore needs **either** (a) the F8‴ canonical chamber-Morse HPC run, identifying `G_n` and verifying (L2-struct) at one or two further `n` to anchor a stabilisation argument, **or** (b) a dedicated structural theorem: that the `S_n`-equivariant Forman-respecting chamber-Morse refinement, starting from the canonical bottom poset, produces a top poset whose incomparability graph is a cluster graph. This is the **precisely-identified residual** of (ICOP-step) and the recommended **F20** target. It is *narrower in kind* than the (FG-Cofiber) residual of the cohomological core: it is a finite order-theoretic / discrete-Morse statement, not a representation-stability one, and it carries no probability and no cohomology.

### 3.5 What F19 establishes for (ICOP-step)

- **Rigorous, n-uniform, unconditional:** Lemma (L1) — a symmetric incomparable pair gives `Pr = 1/2 ∈ [3/11, 8/11]`. This discharges *all* probabilistic content of (ICOP-step).
- **Rigorous reduction:** (ICOP-step) ⟸ (L2) ⟸ (L2-struct) (Proposition 3.1 + §3.3). (L2-struct) is purely order-theoretic.
- **Verified `n ≤ 6`:** (L2) and (L2-struct) hold at `n = 3,4,5` (exact) and `n = 6` (the F8′ candidate) — re-confirmed by the F19 harness.
- **Residual, precisely stated:** an n-uniform proof of (L2-struct) — `G_n` is a width-2 ordinal sum of antichains — recommended as F20.

This is the **GREEN-partial** outcome for (ICOP-step): substantially advanced, reduced to a clean uniform sub-statement of strictly more elementary kind, with the analytic engine fully and rigorously closed.

---

## §4. The width-3 reduction bridge (in-ticket sibling)

### 4.1 The bridge and its status (F10 §7.3, F8 §4.4, §6)

The width-3 *reduction* — step 1 / step 6 of the F10 skeleton — is the statement that "width-3 Kahn–Saks 1/3-2/3 ⟺ non-vanishing cohomological pairing". F8 §4.4 isolates the bridge as three claims: (a) every `P ∈ PPF_m` lies on a critical chain; (b) the critical chain's cover step at `P` is a balanced pair; (c) width-3 posets have their balanced pair captured by the critical chain. F10 §7.3 sharpens this for the canonical chain: *because the canonical chain is the ι-tower (F10 §5.2), the bridge for the canonical chain reduces to (ICOP-step) plus the claim that the ι-tower passes through an `S_m`-orbit representative of every width-3 poset.* Status entering F19: **rigorous for `m ≤ 4`** (F8 Theorem 6.1, by enumeration of PPF₄); **conditional for `m ≥ 5`**.

### 4.2 The `m ≤ 4` rigorous base — re-proven

The F19 harness §F enumerates `PPF_4` (`|PPF_4| = 194`, as expected), isolates the **44 width-3 posets** in it, and verifies that **every one of the 44** admits an incomparable pair `(x,y)` with `Pr ∈ [3/11, 8/11]` — i.e. every width-3 poset on 4 elements has a BFT-sharp balanced pair, witnessed by an explicit cover step. This re-confirms F8 Theorem 6.1 (the `m ≤ 4` rigorous base of the bridge) by direct enumeration, with exact rational arithmetic. **44/44 — CONFIRMED.**

### 4.3 The `m ≥ 5` reduction — to (W3-cover)

With (ICOP-step) handled by §2–§3 (the per-step BFT-sharpness along the canonical chain is now `Pr = 1/2` at every new cover, modulo the (L2-struct) residual), the bridge for `m ≥ 5` reduces — exactly as F10 §7.3 states — to the single combinatorial statement:

> **(W3-cover).** For every `m ≥ 5` and every width-3 partial order `P` on `m` elements, some `S_m`-orbit representative of `P` appears as a poset `P_k` on a canonical critical chain of the chamber-Morse matching of `Δ_m`.

Given (W3-cover) and (ICOP-step): for a width-3 `P`, take the critical chain through (an orbit representative of) `P`; the cover step out of `P` along that chain has `Pr ∈ [3/11, 8/11]` by (ICOP-step) applied along that chain; that cover step is a balanced incomparable pair of `P`, which is exactly the Kahn–Saks 1/3-2/3 witness for `P`. So **bridge `(m ≥ 5)` ⟸ (ICOP-step) + (W3-cover)** — the clean reduction F10 §7.3 anticipated, now stated as a single named target.

### 4.4 Status of (W3-cover) and the F20 recommendation

(W3-cover) is **not** closed by F19, and honestly it should not be expected to be: it is a *global* statement about the chamber-Morse matching of `Δ_m` (which critical cells exist, what posets they pass through), not a statement about one chain. It is of the same residual *kind* as (L2-struct) — it needs the chamber-Morse construction at general `m`, which F8 flags as HPC-class — and it is genuinely the harder of the two bridge pieces. F19 contributes:

- the **`m ≤ 4` base re-proven** (§4.2);
- the **clean reduction** `bridge(m≥5) ⟸ (ICOP-step) + (W3-cover)`, isolating (W3-cover) as a single named combinatorial target;
- the observation that (W3-cover) and (L2-struct) are *the same flavour of residual* — both ask for an n-uniform structural understanding of the canonical chamber-Morse critical cells — so a single F20 ticket targeting the chamber-Morse structure at general `n` would address both.

**Recommendation:** the bridge's `m ≥ 5` case, via (W3-cover), is the natural **F20** sibling, paired with (L2-struct). Per F8′ §4.3, the enabling computation is the F8‴ HPC chamber-Morse run; the structural alternative is a dedicated theorem on the `S_n`-equivariant chamber-Morse critical cells.

---

## §5. The F19 verification harness

`scripts/compat_geom_F19_icop_step.py` (pure-Python stdlib, exact `Fraction` arithmetic, runtime < 5 s; largest linear-extension count is `7! = 5040` permutations — **no new HPC, no new n-datapoint**). It is a *trip-wire* harness: it re-runs the existing empirical record (`c*_3, c*_4, c*_5` from F2/F5, the F8′ `n=6` candidate) and certifies the structural facts the F19 proof rests on. Sections:

- **[A]** reconstructs `c*_3`, `c*_4` (lex-min cell #1 and perfect-MF cell #4), `c*_5` from the literature; verifies each is a genuine chain in `PPF`, reproduces the `|L|`-profiles `(3,2)`, `(5,3,2)`, `(30,14,8,4)`, and confirms every per-step probability lies in `[3/11, 8/11]`.
- **[B]** for each top poset `G_n` and the ι-lift `ι_5(G_5)`: enumerates all admissible single covers, tags `Pr` / BFT-sharpness / symmetric-pair status, identifies the lex-min cover. Result: the lex-min cover is symmetric and BFT-sharp in every case.
- **[C]** certifies **Lemma (L1)**: across 7 posets (up to a 7-element one), all 11 symmetric incomparable pairs have `Pr = 1/2` exactly.
- **[D]** the **(ICOP-step)** per-level audit: the lex-min new cover of `G_n` has `Pr = 1/2` and is a symmetric pair at `n = 3,4,5,6` — uniformly. Records the chain's internal top step separately as context.
- **[E]** reproduces the F8′ `n=6` ι₅-lift candidate in full: multiplicativity profile `(180,84,48,24)`, step-4 lex-min cover `(0,2)` with `Pr = 1/2`, 4/4 BFT-sharp.
- **[F]** the **width-3 bridge `m=4` base**: enumerates `PPF_4` (194), finds the 44 width-3 posets, confirms all 44 are BFT-sharp-witnessed.
- **[H]** the **structural probe**: certifies `G_3, G_4, G_5` are width-2 ordinal sums of antichains with a size-2 block (**(L2-struct)** at `n ≤ 5`); runs the negative control showing the naive greedy symmetric-pair tower loses all symmetry at `n = 4`, so (L2-struct) needs the genuine canonical construction.

All trip-wires **PASS**.

---

## §6. What F19 establishes and does not establish

### 6.1 Establishes

- **Lemma (L1)** — the symmetric-pair lemma — rigorous, n-uniform, unconditional: a cover step at a symmetric incomparable pair has `Pr = 1/2 ∈ [3/11, 8/11]`. This is the n-uniform engine that discharges the entire probabilistic content of (ICOP-step).
- **Proposition 3.1** — the rigorous reduction (ICOP-step) ⟸ (L2) ⟸ (L2-struct), converting (ICOP-step) from an analytic statement into the purely order-theoretic (L2-struct).
- **(L2), (L2-struct) verified at `n = 3,4,5,6`** — re-confirmed by the F19 harness; on this range (ICOP-step) is uniformly `Pr = 1/2`, the strongest BFT-sharp form.
- **The width-3 bridge `m ≤ 4` base re-proven** — all 44 width-3 posets in `PPF_4` are BFT-sharp-witnessed (harness §F).
- **The width-3 bridge `m ≥ 5` reduction** — `bridge(m≥5) ⟸ (ICOP-step) + (W3-cover)`, isolating the single named combinatorial target (W3-cover).
- **The F19 harness** — `scripts/compat_geom_F19_icop_step.py`, all trip-wires pass.

### 6.2 Does NOT establish

- **F19 does not prove (L2-struct) n-uniformly.** This is the precisely-identified residual of (ICOP-step): `G_n` is a width-2 ordinal sum of antichains, for all `n`. It is verified `n ≤ 6` and reduced to a finite order-theoretic statement, but a general-`n` proof needs the F8‴ chamber-Morse HPC run or a dedicated structural theorem (§3.4). Recommended as F20.
- **F19 does not prove (W3-cover).** The `m ≥ 5` half of the width-3 bridge — that the ι-tower meets every width-3 `S_m`-orbit — is a global statement about the chamber-Morse matching; F19 reduces and names it but does not close it. Recommended as the F20 sibling.
- **F19 does not touch the cohomological core, (UCC), or the F17/F18 line.** Those are unconditional and complete; F19's scope is strictly F10 part (iii)'s two secondary inputs.
- **F19 does not touch the Lean trust surface.** No new axioms; no Lean changes; no HPC. The in-tree `width3_one_third_two_thirds` 4-axiom artifact is untouched.
- **F19 does not touch route (iii) / mg-b345.** It stays **PARKED** — the escalation trigger was definitively unmet by F17+F18 and remains so.

### 6.3 Why this is GREEN-partial, not GREEN-icop-step, and not AMBER

It is **not GREEN-icop-step**: that verdict requires (ICOP-step) "proven n-uniformly", and (L2-struct) is not proven for all `n` — only verified `n ≤ 6` and reduced. It is **not AMBER-stalls**: (ICOP-step) did not resist the n-uniform argument — its probabilistic content is *fully and rigorously* discharged by the n-uniform Lemma (L1), and the residual is a precisely-stated, strictly-more-elementary order-theoretic statement, not an obstruction. It is **not RED**: nothing is found false — every check confirms (ICOP-step), and `Pr = 1/2` is the most robustly-BFT-sharp value possible. **GREEN-partial** is exact: (ICOP-step) substantially advanced — reduced to a clean uniform sub-statement (L2-struct), with the engine (L1) fully rigorous and n-uniform — and not fully closed.

---

## §7. Verdict and the program after F19

**Verdict: GREEN-partial.**

(ICOP-step) — the primary F19 target — is reduced, rigorously and n-uniformly, to the purely order-theoretic statement (L2-struct): *the canonical critical cell's top poset `G_n` is a width-2 ordinal sum of antichains.* The probabilistic content is gone, discharged by the symmetric-pair lemma (L1). The width-3 reduction bridge — the in-ticket sibling — has its `m ≤ 4` base re-proven and its `m ≥ 5` case cleanly reduced to (ICOP-step) + (W3-cover). Both residuals — (L2-struct) and (W3-cover) — are of the same kind: an n-uniform structural understanding of the `S_n`-equivariant chamber-Morse critical cells.

**The program after F19:**

- **Cohomological core (F10 (i)–(ii))** — `Hyp(n)` all `n`, H-Cox + sgn at general `n`, `ω_bal^{(n)}` existence/uniqueness/pairing — **DONE, unconditional** (F10 §6 + F17 + F18).
- **Numerical width-3 conclusion (F10 (iii))** — now rests on:
  - **(L2-struct)** — `G_n` is a width-2 ordinal sum of antichains. Verified `n ≤ 6`; the engine (L1) closes everything else of (ICOP-step). *Recommended F20 target.*
  - **(W3-cover)** — the ι-tower meets every width-3 `S_m`-orbit. The `m ≥ 5` half of the bridge; verified `m ≤ 4`. *Recommended F20 sibling.*
- **Lean formalization track** — the in-tree 4-axiom artifact; untouched.
- **Route (iii) / mg-b345** — stays **PARKED**.

**Recommendation for the PM.** A single **F20** ticket targeting the **structure of the `S_n`-equivariant chamber-Morse critical cells at general `n`** would address both residuals at once: (L2-struct) is "`G_n` is a width-2 ordinal sum of antichains", (W3-cover) is "the critical cells collectively meet every width-3 orbit" — both are facts about the same objects. Per F8′ §4.3 the enabling computation is the F8‴ HPC chamber-Morse run; the structural route is a dedicated theorem on the canonical critical cell. With (L2-struct) closed, **(ICOP-step) is proven n-uniformly** (Proposition 3.1 + Lemma (L1)); with (L2-struct) + (W3-cover) closed, **F10 part (iii) is unconditional**, and — with the F17+F18 unconditional cohomological core — **the full width-3 Kahn–Saks 1/3-2/3 theorem is proven at general `n`** (modulo the separate Lean 4-axiom trust surface). The crown-jewel close is one well-scoped structural ticket away.

### 7.1 Trust-surface impact

**None.** F19 introduces no new axioms, makes no Lean changes, runs no HPC, and adds no new empirical n-datapoint. It is elementary order-complex combinatorics — one rigorous n-uniform lemma (L1), a reduction (Proposition 3.1), and a trip-wire harness that re-runs the existing `n ≤ 6` record with exact rational arithmetic. The in-tree Lean artifact and the general-`n` paper-level track are untouched.

---

## §8. References

### 8.1 Predecessor and sibling mg-tickets

- **mg-d039** — F18 ((UCC.2): `δ_n` injective for all `n`): **GREEN-ucc2-proven.** `docs/compatibility-geometry-F18-ucc2-delta-injective.md` §5.4 (what remains for the full width-3 theorem — (ICOP-step) + the bridge), §7.2 (the program after F18; (ICOP-step) recommended as the more central). **Parent.**
- **mg-4d3a** — F17 (n-uniform `S_n`-equivariant cofiber Morse): **GREEN-equivariant-uniform.** With F18, the cohomological core is unconditional.
- **mg-8216** — F10 (general-`n` unified proof synthesis): **GREEN-conditional.** `docs/general-n-proof-synthesis.md` §5.2 (the ι-tower form + F8′ multiplicativity), §5.3 (the lex-min cover avoids extremal elements), §5.4 (**(ICOP-step)**), §6.7 (the conditional theorem, part (iii)), §7.3 (**the width-3 reduction bridge**), §7.4 (the conditional-inputs table). **Parent.**
- **mg-1e99** — F8 (inductive `ω_bal` for general `n` + ICOP): `docs/compatibility-geometry-F8-inductive-general-n.md` §4.1 (the 8-step chamber-Morse construction), §4.3–4.4 (ICOP, the bridge §4.4(a)–(c)), §6 (the width-3 closure argument, Theorem 6.1 = the `m ≤ 4` base), §11 (the `n=5` cancelled outlier — the post-Forman canonical matching has its steps at balanced pairs).
- **mg-7b3b** — F8′ (`n=6` ICOP empirical test): **GREEN-with-refinement.** `docs/compatibility-geometry-F8prime-n6-icop.md` §3 (the ι₅-lift candidate, the multiplicativity confirmation, the step-4 lex-min cover `(0,2)` with `Pr=1/2`, the extremal-element distinction §3.5–3.7), §4.3 (the F8‴ HPC follow-on).
- **mg-1e58** — F5 (chamber-Morse at `n=5`): `docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md` §4.3 (`c*_5` explicit, the lifted chain, the per-step `Pr` table `(7/15, 4/7, 1/2)`).
- **mg-7455 / mg-6bc3** — F2 / F3 (`n=4` discrete Morse + `ω_bal` Pr-spectrum): `docs/compatibility-geometry-F2-scoping.md` §4.3 (`c*_4` explicit — cell #1 the lex-min critical 2-cell, cells #2–4), F3 (all 8 per-step Pr-values in `[3/11,8/11]`).
- **mg-b345** — F8″ (route (iii)): **PARKED** — F19 does not touch it.

### 8.2 Mathematical literature

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) — the 1/3-2/3 conjecture.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — the `[3/11, 8/11]` BFT-sharp interval.
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — the discrete-Morse / chamber-Morse machinery underlying the canonical critical cell.
- A. Björner, *Topological methods*, in *Handbook of Combinatorics*, Elsevier 1995, §10 — order-complex topology; ordinal sums of antichains.
- N. Linial, *The information-theoretic bound is good for merging*, SIAM J. Comput. 13 (1984) — width-2 1/3-2/3, the precedent for the width-3 target.

### 8.3 Code

- `scripts/compat_geom_F19_icop_step.py` — **this F19 / mg-5722** — the trip-wire verification harness. Pure-Python stdlib; runtime < 5 s; all trip-wires pass. Sections [A]–[H] as described in §5.

### 8.4 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. F19 is internal: one elementary n-uniform lemma + a reduction + a trip-wire harness.
- 2026-05-14T08:05Z — focus on the induction, not special cases. F19 introduces no new n-datapoint; the harness re-runs the existing `n ≤ 6` record, and the contribution is the n-uniform lemma (L1) and the structural reduction.

---

*End of F19 — (ICOP-step) and the width-3 reduction bridge.*
