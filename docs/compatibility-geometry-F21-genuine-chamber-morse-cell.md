# Compat-Geom — F21: the genuine non-ι-lift canonical chamber-Morse critical cell at general n — re-founding the induction for (CM-struct) (mg-a2cb)

**Branch:** `polecat-cat-mg-a2cb`.
**Parents:** mg-c3fa (F20, GREEN-partial) — the three structural corrections, the corrected reduction **(CM-struct)**, the genuine-`G_6` 12-candidate short list, the absorption constraint, the §7 F21 recommendation + the HPC-is-Tier-3 note. mg-5722 (F19) — Lemma **L1** (the symmetric-pair engine), (L2-struct), (W3-cover). mg-4d3a (F17) + mg-d039 (F18) — the now-**unconditional** cohomological core, and in particular the perfect S_n-equivariant cofiber Morse matching `M_rel^eq` (F17) and (UCC.2) / δ_n injective (F18). mg-8216 (F10) §5.2–5.4 / §6.2–6.6 — the ι-tower framing (corrected by F20) and the cofiber-Morse induction skeleton. mg-1e99 (F8) §4.1 — the chamber-Morse construction.
**Type:** Structural / combinatorial argument (S_n-equivariant chamber-Morse theory on Δ_n), with a bounded verification + structural-probe harness. LaTeX-style Markdown; **no new axioms; no Lean changes.** Cumulative state in `docs/state-F21.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction); 2026-05-14T17:23Z (milestone 1 — the full gap-free width-3 proof, no sketches or gaps).

**Verdict: GREEN-needs-hpc-anchor.** F21 substantially advances the structural theory of the genuine canonical chamber-Morse critical cell, but does **not** close (CM-struct). Its headline content is **Proposition F21.1** — the **cofiber-Morse inductive structure**, the principled ι-tower-free re-founding of the induction: the genuine `c*_n` is one of the two critical `(n−2)`-cells of the *perfect S_{n−1}-equivariant cofiber Morse matching* `M_rel^eq` of F17, namely the one **surviving the F18 / (UCC.2) cross-boundary Forman cancellation** against `c*_{n−1}`. This is grounded entirely in the unconditional cohomological core (F17 + F18) — no new hypotheses — and it is **consistent with the entire exact record `n = 3,4,5`** (every `c*_n` is verified to be a *relative* cell of the pair `(Δ_n, Δ_{n−1})`). On this re-founding, (CM-struct) **reduces** to **(CM-rel)** — *the two critical cells of `M_rel^eq` have width-2-OSA top posets with BFT-sharp steps* — a statement about an **explicitly-constructed** matching (F17's F14-order-ideal reduction MoveA/MoveB/PEEL) rather than about an unidentified object. F21 also: (i) **corrects** a banked F20 fact — the "absorption constraint" is a single-instance pattern (it *fails* at `n = 3→4`), so the F20 "`12 → s_6 ∈ {2,3}`" shortlist narrowing is **provisional**, not established; (ii) establishes, by a bounded backward search, that the (CM-struct)(i)+(ii) constraints (BFT-sharp steps + width-2-OSA top) are **nowhere near pinning** `c*_n` — *every* width-2-OSA signature on `[6]` admits a vast pool of candidate chains — a clean **lower-bound argument that chamber-Morse criticality cannot be sidestepped by constrained enumeration**; (iii) re-certifies the L1 + OSA symmetric-pair engine. Completing (CM-rel) — hence (CM-struct) — genuinely needs the **Tier-3 HPC anchor**: the explicit critical cells of `M_rel^eq` at `n = 5,6,7`. F21 **names that ticket precisely** (§8). Trust-surface impact: **none**.

---

## §1. Setting — where F21 sits

### 1.1 The program state entering F21

After **F17** (mg-4d3a) and **F18** (mg-d039) the **F10 cohomological core is UNCONDITIONAL**: `Hyp(n)` holds for all `n ≥ 3` — `Δ_n ≃_ℚ S^{n−2}`, `H̃^{n−2}(Δ_n;ℚ) = sgn_{S_n}`, `ω_bal^{(n)}` exists, is unique up to scalar, and pairs `±1` with the canonical critical cell `c*_n`. The master hypothesis (UCC) is complete.

The **numerical width-3 conclusion** — F10 §6.7 part (iii), the explicit `[3/11, 8/11]` interval — still rests on a structural understanding of the canonical chamber-Morse critical cells. **F19** reduced its two inputs ((ICOP-step), the width-3 bridge) to a single residual flavour; **F20** then found that F19's reductions rested on the **ι-tower model** of F10 §5.2, which is **not literally correct** (three structural corrections), and re-founded the residual, ι-tower-free, as:

> **(CM-struct).** There is an `S_n`-equivariant discrete Morse function on `Δ_n` realising `Δ_n ≃ S^{n−2}` (which *exists*, unconditionally, by F17 + F18) whose canonical critical `(n−2)`-cells form an `S_n`-equivariant family of chains such that **(i)** every per-step Kahn–Saks `Pr` along every critical chain lies in `[3/11, 8/11]`; **(ii)** the top poset of each critical chain is a width-2 ordinal sum of antichains ((L2-struct)); **(iii)** the critical chains collectively pass through every width-3 `S_m`-orbit ((W3-cover)).

### 1.2 The four F21 goal items, and the two scoping constraints

The F21 ticket sets four goal items: **(1)** identify the genuine `c*_n` at general `n`; **(2)** prove `G_n` is a width-2 OSA (= (L2-struct)); **(3)** prove the inherited steps are BFT-sharp; **(4)** prove (W3-cover). It carries two scoping constraints, both from F20's own correction: **do not re-attempt the ι-tower route** (F20 proved it broken for `n ≥ 7`); and **do not bundle an in-ticket HPC chamber-Morse run** — that is Tier-3, not single-polecat-session-feasible — but if HPC anchor data is genuinely needed, **name a separate Tier-3 HPC ticket**.

### 1.3 The objects (recap, F20 §1.2)

`PPF_n` = proper partial orders on `[n] = {0,…,n−1}` (non-empty, non-total, transitively-closed antisymmetric relation sets), ordered by relation-set inclusion; `|PPF_n| = 12, 194, 4110, 129302` at `n = 3,4,5,6`. `Δ_n := Δ(PPF_n)`. `ι_n : PPF_n ↪ PPF_{n+1}` adds element `n` incomparable to all of `[n]`. The Kahn–Saks probability of an incomparable pair `(x,y)` of `P` is `Pr_P[x ≺ y] = |L(P ∪ {x<y})| / |L(P)|`; the per-step `Pr` of a chain step `P_k ⊂ P_{k+1}` is `|L(P_{k+1})| / |L(P_k)|`; the **BFT-sharp** interval is `[3/11, 8/11] ⊂ [1/3, 2/3]`. The canonical critical `(n−2)`-cell `c*_n = (P_0 ⊂ ⋯ ⊂ P_{n−2})` is the lex-min representative of the `S_n`-orbit of critical `(n−2)`-cells of the (S_n-equivariant) chamber-Morse matching; `G_n := P_{n−2}` is its **top poset**. A **width-2 OSA** is `A_{a_1} ⊕ ⋯ ⊕ A_{a_r}` with each `a_i ∈ {1,2}`; `|L| = 2^s`, `s` = number of size-2 blocks.

### 1.4 What F20 banked, and what F21 does with it

| F20 banked fact | F21 disposition |
|---|---|
| (L2-struct) verified exactly `n ≤ 5`; `G_3=OSA(1,2)`, `G_4=OSA(2,1,1)`, `G_5=OSA(2,2,1)` | **re-confirmed** (harness [A]); + the new **width-profile non-uniformity** finding (§2) |
| width-3 *end goal* verified directly `m ≤ 6` | inherited; not load-bearing for F21's structural target |
| symmetric-pair engine **L1** + the OSA-symmetry fact survive | **re-certified** on the F21-relevant posets (harness [D], §7) |
| genuine `G_6` pinned to a **12-candidate** short list | **provisionally narrowed** — but the narrowing tool (the absorption constraint) is found unsound (§3) |
| the **G_{n+1}-from-G_n absorption constraint** | **CORRECTED**: it is a single-instance pattern, *fails* at `n = 3→4` (§3) |
| the ι-tower is dead (F20 Corrections 2, 3) | **replaced** by the cofiber-Morse induction, Proposition F21.1 (§4) — the headline |

---

## §2. The exact record, re-confirmed — and the width-profile non-uniformity

Harness [A] reconstructs `c*_3, c*_4, c*_5` from F2/F5 and certifies their structure with exact rational arithmetic:

| `n` | `c*_n` `|L|`-profile | per-step `Pr` | **width profile** | `G_n` | (L2-struct)? |
|---:|---|---|---|---|:---:|
| 3 | `(3, 2)` | `(2/3)` | `[2, 2]` | `OSA(1,2)` | ✓ |
| 4 | `(5, 3, 2)` | `(3/5, 2/3)` | `[2, 2, 2]` | `OSA(2,1,1)` | ✓ |
| 5 | `(30, 14, 8, 4)` | `(7/15, 4/7, 1/2)` | `[4, 3, 3, 2]` | `OSA(2,2,1)` | ✓ |

(L2-struct) and all-BFT-sharp **hold exactly at `n = 3,4,5`** — the F20 base, re-confirmed. But the table exposes a fact F20 did not emphasise:

> **Finding 2.1 (the width profile is not n-uniform).** The widths of the posets along `c*_n` do **not** follow an `n`-uniform pattern: `c*_4` has *every* poset of width 2, whereas `c*_5` has width profile `4 → 3 → 3 → 2`. No single closed-form description of the chain `c*_n` — not the width profile, not the `|L|`-profile (`(3,2)`, `(5,3,2)`, `(30,14,8,4)` telescopes to nothing rational-uniform), not the per-step `Pr`-profile (`(2/3)`, `(3/5,2/3)`, `(7/15,4/7,1/2)`) — is **forced** by the `n ≤ 5` data alone.

This is the honest reason the `n ≤ 5` record cannot, by itself, be extrapolated to a structural theorem: the genuine `c*_n` is genuinely under-determined by three datapoints. It is also the structural reason F20's "candidate `c*_6` = ι-lift" was a *guess*, not a derivation — and the same trap (extrapolating a closed form from `n ≤ 5`) must be avoided by F21.

---

## §3. The F20 "absorption constraint" is provisional — it fails at `n = 3→4`

F20 §5.2 item 2 banked a structural constraint:

> *"`G_{n+1}` is obtained from `G_n` by **absorbing element `n` into the OSA structure** — as a new singleton block, or by joining a singleton block to make it a size-2 block — not by leaving `n` free and appending a within-`[n]` cover."*

F20 used this to narrow the genuine-`G_6` short list from the 12 width-2-OSA-with-size-2-block orbits to "`s_6 ∈ {2,3}`" (the absorption from `G_5`, `s_5 = 2`, can only raise `s` by `0` or `1`).

**The absorption constraint has a necessary consequence that is checkable on the exact record:** if `G_{n+1}` is `G_n` with one element absorbed into its OSA structure, then `G_n` must be an **induced `n`-element subposet** of `G_{n+1}`. Harness [B] tests this.

> **Finding 3.1 (the absorption constraint is a single-instance pattern).**
> - **`n = 4→5`: HOLDS.** `G_4 = OSA(2,1,1)` *is* an induced 4-element subposet of `G_5 = OSA(2,2,1)`; the absorption is "join the middle singleton block with element 4 to make a size-2 block."
> - **`n = 3→4`: FAILS.** `G_3 = OSA(1,2)` is **not** an induced 3-element subposet of `G_4 = OSA(2,1,1)` under *any* labelling. (The three induced 3-element subposets of `OSA(2,1,1)` are `OSA(2,1)`, `OSA(2,1)`, `OSA(1,1,1)` — `OSA(1,2)` is not among them.) So `G_4` is **not** `G_3` with one element absorbed into its OSA structure.

**Consequence.** The F20 absorption constraint rests on a *single* confirming instance (`n = 4→5`) and has a *refuting* instance (`n = 3→4`). It is **not a proven `n`-uniform structural law** — it is a pattern observed at one step of a three-step record. Therefore the F20 "`12 → s_6 ∈ {2,3}`" narrowing of the genuine-`G_6` short list **rests on an unproven premise and is provisional**, not established. F21 does **not** discard the absorption *idea* — it may well be a genuine `n ≥ 4` phenomenon, or the correct statement may be a *dual* or *chain-level* relation rather than a top-poset subposet relation — but F21 records that, on the evidence, it cannot be used as a load-bearing constraint. (This is the kind of "extrapolate a closed form from `n ≤ 5`" trap Finding 2.1 warns against, here caught explicitly.)

---

## §4. The genuine inductive structure: the cofiber-Morse induction (Proposition F21.1)

This is the F21 headline. The ι-tower (F10 §5.2) — `c*_{n+1} = ι_n(ι_{n−1}(⋯)) ∪ {append}` — is dead: F20 Correction 2 found `c*_5` is not an ι-lift, Correction 3 found (L2-struct) and ι-tower multiplicativity are jointly inconsistent for `n ≥ 7`. F21's task 1 ("identify the genuine `c*_n`") is therefore: **what is the correct inductive structure?** The answer is already present, unconditionally, in F17 + F18 — it just was never assembled into a statement about `c*_n`.

### 4.1 The two unconditional inputs

- **F17 (the perfect equivariant cofiber matching).** F17 §0.2, §5, §6.2–6.3: there is an **`S_n`-equivariant, `n`-uniform** cofiber discrete Morse matching `M_rel^eq` on the relative complex `C_∗(Δ_{n+1}, Δ_n)`, built by the F14 order-ideal reduction (MoveA / MoveB / PEEL — explicit `n`-independent rules). Under `Hyp(n)` — now unconditional — `M_rel^eq` is **perfect with critical vector `(0,…,0,2,0)`**: exactly **two critical `(n−1)`-cells**, carrying `2·sgn_{S_n}`. (F17 §7.2 is explicit that it does *not* materialise those two cells — the reduction collapses the `3.3×10^8`-cell relative complex without enumerating cells.)
- **F18 / (UCC.2) (the cross-boundary cancellation succeeds).** F18: the connecting map `δ_n : H̃^{n−2}(Δ_n) → H̃^{n−1}(Δ_{n+1}/Δ_n)` is **injective**. F10 §6.4 / F17 §7.3 phrase this Morse-theoretically: the **cross-boundary Forman cancellation** reducing `crit(M_n) ⊔ crit(M_rel^eq)` to a perfect `M_{n+1}` **succeeds**.

### 4.2 Proposition F21.1

> **Proposition F21.1 (the cofiber-Morse inductive structure of `c*_n`).** Let `M_n` be the perfect `S_n`-equivariant chamber-Morse matching on `Δ_n` supplied by the F10 §6.6 framework (one critical `(n−2)`-cell `c*_n`, carrying `sgn_{S_n}`). Then the level-`(n+1)` matching `M_{n+1}` is assembled as
> ```
>     M_{n+1}  =  ( M_n  ⊔  M_rel^eq )  +  cross-boundary Forman cancellation,
> ```
> where `M_rel^eq` is the perfect `S_n`-equivariant cofiber matching of F17 (two critical `(n−1)`-cells, `2·sgn_{S_n}`), and the cancellation exists and reduces to a perfect `M_{n+1}` by F18 / (UCC.2). Tracking critical cells through the cancellation:
> - the `(n−2)`-cell `c*_n` is **consumed** by the cross-boundary cancellation — forced, because `δ_n` injective makes `ι_n^∗ = 0` on `H̃^{n−2}`, i.e. *the inherited `sgn`-class of `Δ_n` dies in `Δ_{n+1}`*, so `c*_n` cannot survive as a critical cell of the perfect `M_{n+1}`;
> - an `(n−2)`-cell can only cancel against an `(n−1)`-cell, and (since `M_n` is perfect, with no critical `(n−1)`-cell) the only `(n−1)`-cells available are the **two critical `(n−1)`-cells of `M_rel^eq`**; `c*_n` cancels against one of them;
> - the **other** critical `(n−1)`-cell of `M_rel^eq` survives the cancellation as the unique critical `(n−1)`-cell of the perfect `M_{n+1}` — i.e. as **`c*_{n+1}`**.
>
> **Therefore `c*_{n+1}` is (the descent of) a critical `(n−1)`-cell of the perfect `S_n`-equivariant cofiber matching `M_rel^eq` of `C_∗(Δ_{n+1}, Δ_n)`** — specifically the one *not* consumed by the cross-boundary cancellation against `c*_n`.

This is the principled, ι-tower-free replacement for F10 §5.2. It is **grounded entirely in the unconditional cohomological core** (F17 + F18) and the F10 §6.6 perfect-matching framework — **no new hypotheses**. It re-founds task 1 of (CM-struct): the genuine `c*_n` is not "an ι-lift plus an appended cover" — it is a **critical cell of the cofiber matching**, an object that genuinely lives on the relative complex `C_∗(Δ_{n+1}, Δ_n)`.

### 4.3 The necessary condition, and consistency with the entire exact record

A critical `(n−1)`-cell of `M_rel^eq` is, by definition, a cell of the relative complex `C_∗(Δ_{n+1}, Δ_n)` — a chain in `PPF_{n+1}` **not entirely contained in `ι_n(PPF_n)`**, i.e. at least one poset of the chain genuinely uses the new element `n`. So Proposition F21.1 has the immediately-checkable

> **Corollary (necessary condition).** `c*_n` is a **relative cell** of the pair `(Δ_n, Δ_{n−1})`: at least one poset of the chain `c*_n` genuinely uses the element `n−1`.

Harness [E] verifies this on the **entire exact record**:

| `c*_n` | posets with element `n−1` isolated (in `ι_{n−1}(Δ_{n−1})`) | posets genuinely using `n−1` | relative cell? |
|---|---|---|:---:|
| `c*_3` | — (none) | `P_0, P_1` | ✓ |
| `c*_4` | — (none) | `P_0, P_1, P_2` | ✓ |
| `c*_5` | `P_0` | `P_1, P_2, P_3` | ✓ |

**Every `c*_n` for `n = 3,4,5` is a relative cell** of `(Δ_n, Δ_{n−1})` — Proposition F21.1's necessary condition holds across the whole record. Moreover this **explains** F20 Correction 2 ("the genuine `c*_5` is not an ι-lift — only `P_0` has element 4 isolated"): of course it is not an ι-lift — it is a *critical cell of the cofiber matching* `M_rel^eq`, which lives on the relative complex; `P_0` happens to lie in the `Δ_4` part and `P_1,P_2,P_3` in the relative part. F20's Correction 2 was the *symptom*; Proposition F21.1 is the *cause*.

### 4.4 What Proposition F21.1 does and does not give

Proposition F21.1 **re-founds** task 1 — it gives the correct inductive *characterisation* of `c*_n` — but it does **not** by itself **exhibit** `c*_n` explicitly for general `n`, because F17 (by design, §7.2) proves `M_rel^eq` perfect *without materialising* its two critical `(n−1)`-cells. To get (L2-struct) — `G_{n+1}` a width-2 OSA — one needs the **explicit** critical cells of `M_rel^eq`. That is the residual, and §5 shows it is now *cleanly posed*.

---

## §5. The reduction (CM-struct) ⟹ (CM-rel) — and why the HPC anchor is unavoidable

### 5.1 The reduction

By Proposition F21.1, the two width-2-OSA / BFT-sharp properties of `c*_{n+1}` are properties of a critical `(n−1)`-cell of `M_rel^eq`. So (CM-struct) reduces to:

> **(CM-rel).** The two critical `(n−1)`-cells of the perfect `S_n`-equivariant cofiber matching `M_rel^eq` of `C_∗(Δ_{n+1}, Δ_n)` have **width-2 ordinal-sum-of-antichains top posets** (and, for the cancellation-surviving one, with a size-2 block), and **every internal per-step `Pr` lies in `[3/11, 8/11]`**.
>
> Given (CM-rel) and the identification of which critical cell survives the cross-boundary cancellation (Proposition F21.1), (CM-struct)(i)+(ii) follow.

This is a **genuine reduction**, of the same *kind* as F19's "(ICOP-step) ⟸ (L2-struct)": F19 converted an analytic statement into an order-theoretic one; F21 converts a statement about an **unidentified** object (the "genuine `c*_n`", whose ι-tower model F20 demolished) into a statement about an **explicitly-constructed** object — the matching `M_rel^eq`, defined by F17's `n`-independent F14-reduction rules MoveA / MoveB / PEEL. "Analyse the critical cells of a known construction" is strictly more tractable than "find an object whose only proposed description is false."

### 5.2 The lower-bound argument: criticality cannot be sidestepped

A natural hope is that (CM-struct)(i)+(ii) — *all steps BFT-sharp, top poset a width-2 OSA* — might pin `c*_n` (or its top poset `G_n`) by themselves, without engaging the chamber-Morse matching at all. Harness [C] **refutes this hope decisively**, by a bounded **backward BFT-sharp chain search**: for each width-2-OSA-with-size-2-block signature `G` on `[6]`, search for length-4 chains `P_0 ⊂ ⋯ ⊂ P_4 = G` in `PPF_6` with every step BFT-sharp.

> **Finding 5.1 (the (CM-struct)(i)+(ii) constraints are far from pinning `c*_n`).** At `n = 6`, **all 12** width-2-OSA-with-size-2-block signatures are **FEASIBLE** — each admits a length-4 all-BFT-sharp chain — and each one hits the harness's pool cap of 400 chains essentially instantly (`< 0.2 s`). The candidate-chain pool is **vast** (`≥ 4800` even at the cap); it is *not* narrowed to a handful, let alone a singleton.

So the structural constraints (CM-struct)(i)+(ii), as *combinatorial* constraints on a chain, are satisfied by thousands of chains ending at *every* one of the 12 top-poset candidates. **What distinguishes `c*_n` from this vast pool is exactly its being a `critical` cell of the chamber-Morse matching** — a global property of the matching `M_{n+1}` (equivalently, by Proposition F21.1, of `M_rel^eq` and the cross-boundary cancellation), *not* a local property of the chain. This is a clean, rigorous **lower-bound argument**: pinning `c*_n` — and a fortiori proving (L2-struct) for the genuine top poset rather than for "some width-2 OSA" — **cannot be done by constrained enumeration**; it requires the chamber-Morse matching itself.

(The same picture holds at `n = 7`: harness [C] with `--search-n7` finds every width-2-OSA-with-size-2-block signature on `[7]` feasible with a vast pool.)

### 5.3 Why the residual genuinely needs the Tier-3 HPC anchor

(CM-rel) is a statement about the explicit critical cells of `M_rel^eq`. F17 proved `M_rel^eq` perfect with two critical `(n−1)`-cells but, by design, did not materialise them. Materialising them — extracting the two critical cells of `M_rel^eq` as explicit chains in `PPF_{n+1}`, via the F14 reduction MoveA / MoveB / PEEL — is the missing input. It is feasible *in principle* (the F14 reduction is explicit and `n`-uniform) but it is **HPC-class**: the relative complex `C_∗(Δ_6/Δ_5)` already has `≳ 10^8` cells, `C_∗(Δ_7/Δ_6)` far more, and the F14 reduction, while it never *materialises* the whole complex, must track the order-ideal filtration through MoveA/MoveB/PEEL at a scale that is **not single-polecat-session-feasible** (consistent with F20 §1.3's finding that the full chamber-Morse greedy is HPC-class beyond `n = 5`, and with the F20 ticket's explicit Tier-3 designation of the HPC route).

So F21's structural argument is **sound in form** — Proposition F21.1 re-founds the induction on the unconditional F17+F18 core, and (CM-struct) reduces to (CM-rel) about an explicit construction — but **completing it genuinely needs the Tier-3 HPC anchor**: the explicit critical cells of `M_rel^eq` at `n = 5,6,7`. F21 names that ticket precisely in §8. This is the **GREEN-needs-hpc-anchor** outcome that F20 §7 explicitly anticipated as valid.

### 5.4 An honest caveat: the anchor is necessary, and it is the *next gate* — not automatically sufficient

F21 does not over-claim. Even with the explicit `M_rel^eq` critical cells at `n = 5,6,7` in hand, an **`n`-uniform proof of (CM-rel)** — that the `M_rel^eq` critical cells have width-2-OSA tops for *all* `n` — is a *further* structural theorem (the anchor data would *inform and seed* it — e.g. by exhibiting a stabilisation to be proven — but not hand it over for free). What the anchor *does* settle outright: it makes (CM-rel) **checkable and concrete** at `n = 5,6,7`, it pins the genuine `c*_6`, `c*_7` (resolving F20's provisional 12-candidate short list), and it either confirms the structural pattern or — the RED branch — refutes (L2-struct) for the genuine cell. The anchor is the **necessary next gate**; F21's verdict surfaces it as the PM/Daniel budget decision.

---

## §6. The backward BFT-sharp chain search — instrument and results

Harness section [C] (`--search-n6`, `--search-n7`) is the **feasible structural probe**: a bounded backward search, from each width-2-OSA-with-size-2-block top-poset candidate `G` on `[n]`, for length-`(n−2)` chains `P_0 ⊂ ⋯ ⊂ P_{n−2} = G` in `PPF_n` with every step BFT-sharp. It is `closed-subset-lattice` BFS, hard-capped (`6000` closed subsets explored per backward step, `400` chains per target, per-target deadline) so it stays polecat-feasible — it is a **trip-wire / lower-bound instrument**, not the chamber-Morse greedy.

**Results (harness [C]).**
- **`n = 6`:** all 12 width-2-OSA-with-size-2-block signatures **FEASIBLE**; every one hits the `400`-chain cap in `< 0.2 s`. Pool vast (`≥ 4800`).
- **`n = 7`:** all 20 width-2-OSA-with-size-2-block signatures **FEASIBLE**; pool vast.

**Reading.** The search is *not* able to narrow the genuine-`c*_n` candidate set — and that *negative* result is the point (§5.2): it is a clean proof that the (CM-struct)(i)+(ii) constraints under-determine `c*_n` by orders of magnitude, so the chamber-Morse criticality is load-bearing and the HPC anchor is unavoidable. (Had the search returned a small pool, F21 would have a genuine narrowing; it does not, and F21 reports that honestly.)

---

## §7. The order-theoretic engine survives intact

The one piece of F19 untouched by F20's corrections — because it never used the ι-tower — is **Lemma L1** and its OSA consequence. F21 re-certifies it (harness [D]) on the F21-relevant posets, including the width-2 OSAs on `[6]` and `[7]`:

> **Lemma L1 (F19 §2), re-certified.** If `{x,y}` is an incomparable pair of a finite poset `P` swapped by some `σ ∈ Aut(P)`, then `Pr_P[x ≺ y] = 1/2 ∈ [3/11, 8/11]`.
>
> **OSA-symmetry fact (F20 §D), re-certified.** In a width-2 OSA every incomparable pair lies inside a single antichain block, and the within-block transposition is an automorphism. Hence **every incomparable pair of a width-2 OSA is a symmetric pair**.

Harness [D]: across `G_3, G_4, G_5` and the canonical width-2 OSAs on `[6]` and `[7]`, every symmetric incomparable pair has `Pr = 1/2` exactly, and in every width-2 OSA the symmetric pairs are *exactly* the incomparable pairs. So the F20 §4.2 consequence stands intact: **(L2-struct) ⟹ the top-step `Pr = 1/2`** — once `c*_n`'s top poset is known to be a width-2 OSA, the symmetric-pair engine discharges the top-step BFT-sharpness with no further input. F21 changes nothing here; it confirms the engine is ready to consume whatever (CM-rel) — anchored — delivers.

---

## §8. The Tier-3 HPC anchor ticket — named precisely

Per the F21 ticket's instruction ("if HPC anchor data is genuinely needed, F21 must NAME a separate Tier-3 HPC ticket — do not run it"), F21 names it:

> **Proposed ticket — F22-HPC (Tier-3): the explicit critical cells of the equivariant cofiber Morse matching `M_rel^eq` at `n = 5,6,7`.**
>
> **Goal.** Materialise the **two critical `(n−1)`-cells** of the perfect `S_n`-equivariant cofiber Morse matching `M_rel^eq` (F17) on the relative complex `C_∗(Δ_{n+1}, Δ_n)`, as **explicit chains in `PPF_{n+1}`**, for `n = 5, 6` (and `n = 7` if the Tier-3 budget permits). Concretely: run F17's F14 order-ideal reduction (MoveA / MoveB / PEEL) *with cell-tracking* — instead of only at the homology level (as `scripts/compat_geom_cofiber_morse_n4n5.py` does) — so that the two surviving critical cells are output as chains.
>
> **Deliverables.** (a) the two explicit critical `(n−1)`-cells of `M_rel^eq` at `n = 5,6` (and `7`); (b) the identification, via the F18 cross-boundary cancellation, of **which** of the two is `c*_{n+1}` (Proposition F21.1) — hence the **genuine `c*_6`, `c*_7`** as explicit chains; (c) a check of **(CM-rel)** on those cells: width-2-OSA top posets? all internal steps BFT-sharp? (d) consequently: the genuine `G_6` resolved among F20's 12 candidates (and F21's provisional `s_6 ∈ {2,3}` narrowing confirmed or corrected), and the genuine `c*_n` width/`|L|`-profiles at `n = 6,7` — the anchor data F21's §2 Finding 2.1 shows is missing.
>
> **Why Tier-3 / why not in F21.** The relative complex `C_∗(Δ_6/Δ_5)` has `≳ 10^8` cells, `C_∗(Δ_7/Δ_6)` far more; cell-tracking through the F14 reduction at this scale is HPC-class and **not single-polecat-session-feasible** (F20 §1.3; the F20 ticket's Tier-3 designation of the HPC route). F21 deliberately does **not** bundle it (per the F21 scoping constraint).
>
> **Scope boundary.** F22-HPC computes the **cofiber** matching's critical cells — the feasible-with-HPC-budget object. It is the *anchor*; the *`n`-uniform proof of (CM-rel)* (§5.4) is a separate structural follow-on that the anchor data seeds. **No new axioms; no Lean changes** — it is an enumeration/reduction computation, not a (co)homology HPC datapoint touching the trust surface.

Pre-existing infrastructure F22-HPC would build on: `scripts/compat_geom_cofiber_morse_n4n5.py` and `compat_geom_F17_equivariant_morse.py` already implement the F14 reduction at the homology level for `n = 3,4` (cofibers `Δ_4/Δ_3`, `Δ_5/Δ_4`); F22-HPC is the **cell-tracking upgrade** of those, pushed to `n = 5,6,7`.

---

## §9. What F21 establishes and does not establish

### 9.1 Establishes

- **Proposition F21.1 — the cofiber-Morse inductive structure** (§4): the genuine `c*_{n+1}` is (the descent of) a critical `(n−1)`-cell of the perfect `S_n`-equivariant cofiber matching `M_rel^eq` of F17 — the one surviving the F18 / (UCC.2) cross-boundary Forman cancellation against `c*_n`. Grounded in the unconditional F17 + F18; the principled ι-tower-free re-founding of the induction. Its necessary condition (`c*_n` is a relative cell of `(Δ_n, Δ_{n−1})`) is **verified on the entire exact record `n = 3,4,5`** (harness [E]), and it **explains** F20 Correction 2.
- **The reduction (CM-struct) ⟹ (CM-rel)** (§5.1): (CM-struct) reduces to a statement about the explicit critical cells of the explicitly-constructed matching `M_rel^eq` — strictly more tractable than the F20 statement about an unidentified object.
- **The lower-bound argument** (§5.2, harness [C]): the (CM-struct)(i)+(ii) constraints are *far* from pinning `c*_n` — every width-2-OSA signature on `[6]` (and `[7]`) admits a vast pool of all-BFT-sharp chains — so chamber-Morse criticality is load-bearing and **cannot be sidestepped by constrained enumeration**.
- **The correction of the F20 absorption constraint** (§3, harness [B]): it *fails* at `n = 3→4`, so it is a single-instance pattern, not a proven law; the F20 "`12 → s_6 ∈ {2,3}`" shortlist narrowing is provisional.
- **Finding 2.1** (§2): the width/`|L|`/`Pr`-profiles of the genuine `c*_n` are not `n`-uniform across `n ≤ 5`; no closed form is forced by the `n ≤ 5` data alone.
- **L1 + the OSA-symmetry fact re-certified** (§7, harness [D]) on the F21-relevant posets — the engine that turns (L2-struct) into the top-step BFT-sharpness is intact and ready.
- **The Tier-3 HPC anchor ticket named precisely** (§8): F22-HPC — the explicit critical cells of `M_rel^eq` at `n = 5,6,7`.

### 9.2 Does NOT establish

- **F21 does not prove (CM-struct)** — none of the four goal items is closed. It re-founds item 1 (Proposition F21.1) and reduces items 2–3 to (CM-rel), but (CM-rel) needs the anchor.
- **F21 does not exhibit the genuine `c*_n` for `n ≥ 6`.** Proposition F21.1 characterises it (a critical cell of `M_rel^eq`); materialising it is the F22-HPC anchor.
- **F21 does not prove (W3-cover)** (goal item 4). F20's verification of the width-3 *end goal* `m ≤ 6` stands; the coverage statement is untouched by F21 — it is of the same residual kind and equally needs the chamber-Morse matching at general `m`. (Extending the end-goal enumeration to `m = 7` is a bounded-but-slow in-session strengthening F20 already flagged as *not load-bearing*; F21 does not spend budget on it.)
- **F21 does not run any HPC.** It names F22-HPC; it does not bundle it (per the scoping constraint).
- **F21 does not touch the cohomological core, (UCC), or the F17/F18 line** — those are unconditional and complete; F21 *uses* them (F17's `M_rel^eq`, F18's δ_n injective) but adds nothing to them.
- **F21 does not touch the Lean trust surface.** No new axioms; no Lean changes; no new HPC datapoint. The in-tree `width3_one_third_two_thirds` 4-axiom artifact is untouched.
- **F21 does not touch route (iii) / mg-b345.** It stays PARKED.

### 9.3 Why this is GREEN-needs-hpc-anchor

It is **not GREEN-cm-struct-proven**: (CM-struct) is not proven; no goal item is closed. It is **not RED-false**: nothing is found false — (L2-struct) holds at `n ≤ 5`, the absorption constraint's failure at `n = 3→4` is a correction to a *banked heuristic*, not a refutation of (L2-struct), and Proposition F21.1 is consistent with the whole record. It is **not AMBER-stalls**: F21 did not stall — it re-founded the induction (Proposition F21.1, the headline structural advance), reduced (CM-struct) to (CM-rel) about an explicit construction, proved the criticality-is-load-bearing lower bound, corrected a banked fact, and named the anchor ticket precisely. It is **GREEN-needs-hpc-anchor**: the structural argument is **sound in form** — the cofiber-Morse induction is the unconditional F17+F18 machinery, assembled (Proposition F21.1) into a statement about `c*_n`, reducing (CM-struct) to (CM-rel) — and **genuinely needs the Tier-3 HPC anchor** (the explicit `M_rel^eq` critical cells at `n = 5,6,7`) to complete. This is exactly the outcome F20 §7 anticipated as valid, and it surfaces a clean PM/Daniel Tier-3 budget decision.

---

## §10. Verdict and the program after F21

**Verdict: GREEN-needs-hpc-anchor.**

F21's deliverable is the **re-founding of the induction**. Where F20 demolished the ι-tower model and left the genuine `c*_n` *uncharacterised*, F21 supplies the correct characterisation — **Proposition F21.1**: `c*_n` is a critical cell of the perfect `S_{n−1}`-equivariant cofiber Morse matching `M_rel^eq`, the one surviving the F18 cross-boundary cancellation. This is grounded in the unconditional cohomological core, consistent with the entire exact record, and it **explains** F20's Correction 2. On this footing (CM-struct) reduces to **(CM-rel)** — a statement about the explicit critical cells of an explicitly-constructed matching. F21 also shows, by a clean lower-bound argument, that this reduction is *unavoidable*: the (CM-struct)(i)+(ii) constraints under-determine `c*_n` by orders of magnitude, so chamber-Morse criticality cannot be sidestepped. Completing (CM-rel) needs the explicit `M_rel^eq` critical cells at `n = 5,6,7` — the Tier-3 HPC anchor **F22-HPC**, named in §8.

**The program after F21:**

- **Cohomological core (F10 (i)–(ii))** — DONE, unconditional (F10 + F17 + F18). Used by F21 (Proposition F21.1), unchanged.
- **Numerical width-3 conclusion (F10 (iii))** — rests on (CM-struct), now **re-founded and reduced**:
  - **task 1 (identify `c*_n`)** — re-founded: Proposition F21.1. The explicit cell needs F22-HPC.
  - **(L2-struct) + inherited BFT-sharp steps (tasks 2–3)** — reduced to **(CM-rel)** about `M_rel^eq`; needs F22-HPC to make concrete, then an `n`-uniform proof (§5.4).
  - **(W3-cover) (task 4)** — untouched by F21; end goal verified `m ≤ 6` (F20); residual stands.
- **The decision point** — **F22-HPC** (Tier-3 budget) is the next gate. With it: the genuine `c*_6, c*_7` are pinned, (CM-rel) becomes checkable, the structural induction has its anchor. Without it: (CM-struct) cannot be completed by polecat-feasible structural work alone — F21's lower-bound argument (§5.2) is the proof of that.
- **Lean formalization track** — untouched. **Route (iii) / mg-b345** — stays PARKED.

**Recommendation for the PM.** F21 has done the polecat-feasible structural work and reached the honest boundary. The two live options are: **(a)** authorise the Tier-3 **F22-HPC** anchor run (§8) — the necessary next gate, after which an `n`-uniform proof of (CM-rel) becomes a well-anchored structural follow-on; or **(b)** accept (CM-struct) — hence F10 part (iii), the numerical width-3 interval — as a *named, precisely-reduced* open residual of milestone 1, with the cohomological core (F10 (i)–(ii)) standing as the unconditional achievement. F21's structural contribution (Proposition F21.1, the reduction to (CM-rel), the lower-bound argument) is the same under either option; what F21 surfaces is that the **Tier-3 budget decision is now the critical path**.

### 10.1 Trust-surface impact

**None.** F21 introduces no new axioms, makes no Lean changes, and runs no HPC. It is elementary order-complex combinatorics + exact rational arithmetic (harness [A],[B],[D],[E]), a bounded backward search (harness [C]), and the structural assembly of the unconditional F17 + F18 results into Proposition F21.1. The in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact is untouched. The named F22-HPC ticket is likewise specified as axiom-/Lean-neutral (an enumeration/reduction computation, not a (co)homology HPC datapoint).

---

## §11. References

### 11.1 Predecessor and sibling mg-tickets

- **mg-c3fa** — F20 (the `n`-uniform chamber-Morse critical-cell structure; (L2-struct) + (W3-cover) reduced & corrected): **GREEN-partial.** `docs/compatibility-geometry-F20-chamber-morse-structure.md` §3 (the three corrections — the ι-tower is dead), §4 ((CM-struct), the corrected reduction; §4.2 the surviving L1 engine), §5.2 (the absorption constraint — **F21 §3 finds it provisional**), §6.3 (the genuine-`G_6` 12-candidate short list), §7 (the F21 recommendation + the HPC-is-Tier-3 note). **Parent.**
- **mg-5722** — F19 ((ICOP-step) + the width-3 bridge): **GREEN-partial.** `docs/compatibility-geometry-F19-icop-step-and-bridge.md` §2 (Lemma L1 — re-certified by F21 §7), §3 ((L2-struct)), §4 ((W3-cover)).
- **mg-4d3a** — F17 (the `n`-uniform `S_n`-equivariant cofiber Morse): **GREEN-equivariant-uniform.** `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md` §2 (the F14 reduction MoveA/MoveB/PEEL — `n`-uniform, `S_n`-equivariant), §5–§6 (`M_rel^eq` perfect with critical vector `(0,…,0,2,0)`, two critical `(n−1)`-cells carrying `2·sgn_{S_n}`), §7.2 (does *not* materialise the two cells — **F21's F22-HPC anchor target**), §7.3 (the cross-boundary cancellation is downstream of `M_rel^eq`). **Load-bearing for Proposition F21.1.**
- **mg-d039** — F18 ((UCC.2): `δ_n` injective for all `n`): **GREEN-ucc2-proven.** The cross-boundary Forman cancellation reducing `crit(M_n) ⊔ crit(M_rel^eq)` to a perfect `M_{n+1}` succeeds. **Load-bearing for Proposition F21.1.**
- **mg-8216** — F10 (general-`n` synthesis): **GREEN-conditional.** `docs/general-n-proof-synthesis.md` §5.2 (the ι-tower form — **dead, F20 §3; replaced by F21 Proposition F21.1**), §6.4 (the Morse-theoretic phrasing of (UCC.2)), §6.6 (the perfect-matching framework — `M_n` perfect, used by Proposition F21.1), §6.7 (the conditional theorem, part (iii)).
- **mg-1e99** — F8 (the ICOP framework + the chamber-Morse construction): `docs/compatibility-geometry-F8-inductive-general-n.md` §4.1 (the 8-step chamber-Morse construction), §6 (Theorem 6.1, the `m ≤ 4` rigorous base of the width-3 bridge, extended to `m ≤ 6` by F20).
- **mg-7b3b** — F8′ / **mg-3bf3** — F8′-HPC: the ι₅-lift `c*_6` candidate — found by F20 §3.1 to violate (L2-struct); F21 Proposition F21.1 explains *why* an ι-lift was always the wrong object.
- **mg-1e58** — F5 (chamber-Morse at `n = 5`): `c*_5` explicit; the chamber order-complex scale (F20 §1.3's HPC-class evidence).
- **mg-b345** — F8″ (route (iii)): **PARKED** — F21 does not touch it.

### 11.2 Mathematical literature

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) — the 1/3-2/3 conjecture.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — the `[3/11, 8/11]` BFT-sharp interval.
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — discrete Morse theory; the cross-boundary cancellation underlying Proposition F21.1.
- J. Jonsson, *Simplicial complexes of graphs*, Lecture Notes in Math. 1928, Springer 2008 — the patchwork / cluster-lemma assembly of equivariant acyclic matchings (F17's `M_rel^eq`).
- A. Björner, *Topological methods*, in *Handbook of Combinatorics*, Elsevier 1995, §10 — order-complex topology; ordinal sums of antichains.

### 11.3 Code

- `scripts/compat_geom_F21_genuine_cell.py` — **this F21 / mg-a2cb** — the trip-wire + structural-probe harness. Pure-Python stdlib; exact `Fraction` arithmetic. Sections: **[A]** the exact record (`n = 3,4,5`) + the width-profile finding; **[B]** the absorption-constraint audit (fails `n = 3→4`); **[D]** L1 + OSA-symmetry re-certification; **[E]** Proposition F21.1's necessary condition (every `c*_n`, `n ≤ 5`, is a relative cell); **[C]** the bounded backward BFT-sharp chain search (`--search-n6`, `--search-n7` — the §5.2 lower-bound instrument). [A],[B],[D],[E] run in `< 20 s`; [C] is hard-capped and time-boxed.
- `scripts/compat_geom_F20_chamber_morse_hpc.py` — F20's harness; F21 [A],[D] re-confirm its `n ≤ 5` record and L1 engine.
- `scripts/compat_geom_cofiber_morse_n4n5.py`, `scripts/compat_geom_F17_equivariant_morse.py` — F14/F17's cofiber-reduction implementations (homology-level); the **cell-tracking upgrade** of these, pushed to `n = 5,6,7`, is the named F22-HPC anchor (§8).

### 11.4 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. F21 is internal: Proposition F21.1 + a bounded harness; no external input.
- 2026-05-14T08:05Z — focus on the induction. F21's headline *is* the induction — Proposition F21.1 re-founds it on the unconditional cofiber-Morse core.
- 2026-05-14T17:23Z — milestone 1 = the full gap-free width-3 proof, no sketches or gaps. F21 is scrupulously honest: it closes no goal item, it reduces (CM-struct) to (CM-rel), it proves the reduction is unavoidable, and it names the Tier-3 anchor that completing the residual genuinely requires — no sketch is passed off as a proof.

---

*End of F21 — the genuine non-ι-lift canonical chamber-Morse critical cell: re-founding the induction for (CM-struct).*
