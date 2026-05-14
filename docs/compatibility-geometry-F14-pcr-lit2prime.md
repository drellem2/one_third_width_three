# Compat-Geom — F14 / PCR-Lit-2′: the n=4→5 cofiber cohomology B₄ = H̃³(Δ₅/Δ₄) (mg-3839)

**Branch:** `compat-geom-F14-B4-cofiber-cohomology` (new).
**Parent:** mg-b352 (F11, `11a75d6`) §4.6, §6.2 (follow-up B); mg-6295 (PCR-Lit-2) §6.3 — this is mg-6295's own designated follow-up.
**Type:** Constructive computation (HPC-class; memory-efficient discrete-Morse / order-ideal-filtration reduction). **No new axioms; no Lean changes.**
**Verdict:** **GREEN-cofiber-perfect.** The n=4→5 cofiber cohomology is computed (not merely predicted): `b̃_*(Δ₅/Δ₄) = (0,0,0,2,0)`, concentrated in degree 3, and `B₄ = H̃³(Δ₅/Δ₄) = 2·sgn_{S₄}` — exactly the M1+M2 prediction (F10 §10.2) and (UCC.1) at level 4. An explicit 2-element basis of B₄ is delivered. The whole reduction pipeline is re-run for n=3→4 as a trip-wire and reproduces mg-6295's GREEN result `(0,0,2,0) = 2·sgn_{S₃}`. **F15 / entry sub-problem (E2) is unblocked.**

**Deliverables:**
- `docs/compatibility-geometry-F14-pcr-lit2prime.md` (this doc).
- `scripts/compat_geom_cofiber_morse_n4n5.py` (the computation; pure-Python stdlib; runtime ≈ 2–4 min, peak ≈ 8.4 GB).
- `docs/state-F14.md` (cumulative state ledger).

---

## 0. Executive summary

### 0.1 The target and why it is load-bearing

F11 (mg-b352) advanced route (ii): the representation-type half of (UCC.1) reduces to "the triple connecting homomorphism `∂_n : B_n → B_{n+1}` is an isomorphism for all n", where `B_n := H̃^{n-1}(Δ_{n+1}/Δ_n)` is the cofiber-cohomology diagonal. The first concrete test of that hypothesis — entry sub-problem **(E2)**, F15 — is to compute `∂_3 : B_3 → B_4` and test it for isomorphism. `∂_3` is a 2×2 S₃-equivariant matrix between `B_3 = 2·sgn_{S_3}` (known, mg-6295) and `B_4 = H̃³(Δ_5/Δ_4)` — **but B₄ was not yet computed.** F14 computes it.

This is a **gating computation for the general-n route (ii) mechanism**, not a fixed-n datapoint hunt (cf. `feedback_focus_on_induction_not_special_cases`): B₄ is the prerequisite to test the iso hypothesis the entire general-n route hinges on.

### 0.2 Setting (the F1-refined / F2 / F5 / mg-6295 convention)

`Δ_n` is the order complex of `PPF_n := Pos_n^sub \ {antichain} \ {total orders}`. Cardinalities (F10 §1.1): `|PPF_3| = 12`, `|PPF_4| = 194`, `|PPF_5| = 4110`. The inclusion `ι_4 : PPF_4 ↪ PPF_5` sends a partial order on `{0,1,2,3}` to the same relation set on `{0,1,2,3,4}` (element 4 incomparable to all); it is an **order-ideal** inclusion and induces the subcomplex inclusion `Δ_4 ↪ Δ_5`.

### 0.3 Why the naive mg-6295 greedy+Forman recipe does not run at n=4→5

The script computes (by a DP that never materialises the chains) the f-vector of the relative complex `C_*(Δ_5, Δ_4)`:

```
f(Δ_5)              = [4110, 250770, 3476940, 19929720, 58774320, 97333440, 91669440, 45926400, 9515520]
f(Δ_4)              = [194, 1872, 5232, 5664, 2112]
f(C_*(Δ_5,Δ_4))     = [3916, 248898, 3471708, 19924056, 58772208, 97333440, 91669440, 45926400, 9515520]
total relative cells = 326 865 586          χ̃(Δ_5/Δ_4) = −2
```

**3.3 × 10⁸ relative cells.** mg-6295's recipe — materialise every relative cell, build the cover graph (`Σ(k+1)f_k ≈ 10⁹` cover pairs), run a greedy acyclic matching with a per-acceptance reachability DFS — is flatly infeasible at this size (tens of GB; the F9-S2 `solve_psi_fast` thrash failure mode the ticket warns about). F14 therefore uses the **memory-efficient route the ticket asks for**: an S_n-equivariance / order-ideal-filtration reduction. It is itself discrete Morse theory (the cluster lemma — Hersh 2005, Jonsson's patchwork theorem — assembles fibrewise acyclic matchings into a global one), and it collapses the 3.3 × 10⁸-cell relative complex onto a single **1.5 × 10⁷-cell** order complex `Δ(A_4)` without ever materialising the huge complex.

### 0.4 Headline results

| Object | Result | Cross-check |
|---|---|---|
| Trip-wire n=3→4 (full pipeline) | `H̃_*(Δ_4/Δ_3) = (0,0,2,0)` = `2·sgn_{S_3}` | reproduces mg-6295 GREEN |
| Collapse-engine self-test | 4/4 medium complexes: collapse-homology = direct Gaussian | — |
| relative complex `C_*(Δ_5,Δ_4)` | 326 865 586 cells, χ̃ = −2 | DP f-vector |
| **`b̃_*(Δ_5/Δ_4)`** | **`(0,0,0,2,0)`** — concentrated in degree 3 | M1+M2 prediction (F10 §10.2) |
| **`B_4 = H̃³(Δ_5/Δ_4)`** | **`2·sgn_{S_4}`** | (UCC.1) at level 4; equivariant Euler char |
| reduction landmark `Δ(A_4)` | `\|A_4\| = 1420`, 15 166 278 cells, `H̃_* = (0,0,1)` (A_4 ≃ S²) | elementary collapse → residual `(195,606,413)` |
| explicit basis of B₄ | `{z_D, z_U}`, 2 explicit 2-cycles | boundary verified to vanish |

**Verdict: GREEN-cofiber-perfect.** Triggers F15 / (E2).

---

## 1. The reduction (rigorous; every hypothesis verified at run time)

### 1.1 Three operations

The pipeline reduces the cofiber `Δ_5/Δ_4` through a sequence of operations, each of which is a rigorous statement about order-ideal filtrations whose collapse hypothesis is **asserted at run time** (the script raises if a fibre is not contractible/empty/concentrated).

**MoveA (peel element e).** Cofiber `Δ(P)/Δ(Q)` with `Q` an order ideal of `P`. *If* for every `x ∈ R := P\Q` the down-set `Q_{<x}` has `Δ(Q_{<x})` contractible-or-empty, the order-ideal-filtration spectral sequence collapses onto the line `q = −1` and

> `H̃_d(Δ(P)/Δ(Q)) = H̃_d(Δ(R)/Δ(R \ Q_∅))`,  `Q_∅ := {x ∈ R : Q_{<x} = ∅}`,

an order ideal of `R`. (The cluster lemma: the fibrewise "toggle-apex" matchings on the cone fibres assemble to a global acyclic matching; the collapse is exact because the SS is concentrated on a single line.) The new subcomplex `Δ(R\Q_∅)` is a **filter** subcomplex of `R`.

**MoveB.** Cofiber `Δ(P)/Δ(Sub)` with `Sub` an order *filter* of `P`, `A := P\Sub` the complementary order ideal. *If* for every connected component `A^{(j)}` of `Δ(A)` and every `x ∈ Sub` the down-set `A^{(j)}_{<x}` has `Δ` contractible-or-empty, the filtration by `|chain ∩ Sub|` collapses onto `q = 0` and

> `H̃_d(Δ(P)/Δ(Sub)) = ⊕_j H̃_{d-1}(Δ(P^{(j)}))`,  `P^{(j)} := {x ∈ Sub : A^{(j)}_{<x} ≠ ∅}`.

Each summand is an **absolute** reduced homology of a smaller poset, shifted up by one degree.

**PEEL (all-cone homology iso).** For an absolute `H̃_*(Δ(P))`: if an order ideal `Q` of `P` has `Q_{<x}` contractible (**never empty**) for every `x ∈ P\Q`, then `Δ(Q) ↪ Δ(P)` is a homology isomorphism, so `H̃_*(Δ(P)) = H̃_*(Δ(Q))`.

All three are S_n-equivariant: every poset, ideal, fibre and component involved is invariant under `S_n` permuting `{0,…,n−1}` and fixing `n`.

### 1.2 The pipeline for Δ₅/Δ₄

```
H̃_d(Δ_5/Δ_4)
  = cofiber_homology(PPF_5, ι_4(PPF_4),  Q an ideal)
  --[MoveA, peel element 4]-->     |R| = 3916,  |Q_∅| = 30,
                                   218 distinct non-empty fibres, all contractible
  = cofiber_homology(R, R\S,  Sub a filter)
  --[MoveB]-->                     ideal S = R\Sub has |S| = 30,  2 components of size 15
  = H̃_{d-1}(Δ(D_4)) ⊕ H̃_{d-1}(Δ(U_4))     |D_4| = |U_4| = 2442
  --[PEEL, all-cone kill_down_4 / kill_up_4]-->
  = H̃_{d-1}(Δ(A_4)) ⊕ H̃_{d-1}(Δ(A_4'))    |A_4| = 1420,  Δ(A_4) has 15 166 278 cells
```

Here `S = R\Sub` is the "Type-∅" ideal `{x ∈ R : x|_{0123} = ∅}` — the posets whose only relations involve element 4. Its order complex has exactly **2 components**, the "4-below" copy `{x : 4 < B for some ∅≠B⊆{0,1,2,3}}` and the "4-above" copy — each a barycentric subdivision of a 3-simplex. The two components produce the two summands `D_4 = {Down_4 ≠ ∅, x|_{0123} ≠ ∅}` and `U_4 = {Up_4 ≠ ∅, x|_{0123} ≠ ∅}`. The order-reversal involution `(a,b) ↦ (b,a)` is an **S₄-equivariant isomorphism `D_4 ≅ U_4`**, so the two summands are isomorphic as S₄-representations and

> **`H̃_d(Δ_5/Δ_4) = 2 · H̃_{d-1}(Δ(A_4))`**  as S₄-representations,
> `A_4 = {x ∈ PPF_5 : Down_4(x) ≠ ∅, Up_4(x) = ∅, x|_{0123} ≠ ∅}`, `|A_4| = 1420`.

The all-cone peel `kill_up_4` (resp. `kill_down_4`): for `x ∈ D_4` with `Up_4(x) ≠ ∅`, the apex `x^{−up4}` (delete every `(·,4)` relation) lies in `D_4` *for every such x* — deleting in-relations of 4 touches neither `Down_4(x)` nor `x|_{0123}` — so every fibre is a cone, never empty, and the peel is a homology isomorphism.

### 1.3 The terminal complex Δ(A₄) and its homology

`A_4` has no all-cone peel (its two defining conditions `Down_4 ≠ ∅` and `x|_{0123} ≠ ∅` together touch every relation of every element), so `Δ(A_4)` is computed directly. The script materialises its 15 166 278 cells (≈ 3 s), runs an **elementary collapse** (free-face removal — a sequence of valid elementary collapses, since whenever `alive` is a subcomplex and a cell `s` has exactly one alive codim-1 cofacet `t`, that `t` is necessarily a maximal cell and `s` a free face), and computes the homology of the residual core by mod-p Gaussian elimination:

```
direct_big: f = [1420,55094,526020,2119404,4346436,4790208,2709264,618432]  (15 166 278 cells)
  elementary collapse: 15 165 064 cells removed, 1214 survive   res-f = [195,606,413,0,…]
  residual reduced Betti = (0,0,1)
```

So **`H̃_*(Δ(A_4)) = (0,0,1)` — `Δ(A_4) ≃ S²`.** Elementary collapse preserves Euler characteristic, and the script verifies `χ̃(full f-vector) = χ̃(residual) = +1` as a guard; the residual is purely 2-dimensional, forcing `H̃_k(Δ(A_4)) = 0` for all `k ≥ 3` structurally.

---

## 2. The result: B₄ = H̃³(Δ₅/Δ₄)

### 2.1 Betti vector

`H̃_d(Δ_5/Δ_4) = 2·H̃_{d-1}(Δ(A_4))` with `H̃_*(Δ(A_4)) = (0,0,1)` gives

> **`b̃_*(Δ_5/Δ_4) = (0, 0, 0, 2, 0)`** — concentrated in degree 3, `b̃_3 = 2`.

This is exactly the M1+M2 consistency prediction (F10 §10.2). χ̃ = −2 (computed independently from the f-vector) is consistent: `0 − 0 + 0 − 2 + 0 = −2`.

### 2.2 S₄-representation type

The whole reduction is S₄-equivariant, so the equality `H̃_d(cofiber) = 2·H̃_{d-1}(Δ(A_4))` holds as S₄-representations. The script computes the **equivariant Euler characteristic** `χ^{S_4}(Δ(A_4)) = Σ_k (−1)^k [H̃_k]` directly, via the reduced Euler characteristic of the `g`-fixed subposets `Δ(A_4^g)` for one `g` per conjugacy class (Hopf trace formula). The result:

```
χ^{S_4}(Δ(A_4))  = { triv:0, sgn:1, std:0, std⊗sgn:0, V_2:0 }      = sgn_{S_4}
χ^{S_4}(Δ_5/Δ_4) = { triv:0, sgn:−2, std:0, std⊗sgn:0, V_2:0 }     = −2·sgn_{S_4}
```

Since `H̃_*(Δ_5/Δ_4)` is concentrated in degree 3, `χ^{S_4}(cofiber) = (−1)^3 [B_4] = −[B_4]`, hence

> **`B_4 = H̃³(Δ_5/Δ_4) = 2·sgn_{S_4}`** — exactly (UCC.1) at level 4.

Equivalently: `Δ(A_4) ≃ S²` carries `H̃_2(Δ(A_4)) = sgn_{S_4}`, and `B_4 = 2·H̃_2(Δ(A_4)) = 2·sgn_{S_4}`.

### 2.3 Explicit basis of B₄ (deliverable 3)

`B_4 = H̃_2(Δ(D)) ⊕ H̃_2(Δ(U))`, and `H̃_2(Δ(D)) = H̃_2(Δ(A_4))` via the all-cone `Up_4` peel (`A_4 ⊂ D_4 = D`, and the peel is a homology iso, so a 2-cycle of `Δ(A_4)` *is* a generating 2-cycle of `H̃_2(Δ(D))`). The script extracts an explicit generator `z_D` of `H̃_2(Δ(A_4))` as a kernel vector of the residual boundary `∂_2` of the collapsed core — an explicit `ℤ`-combination of triangles (3-chains `P_0 < P_1 < P_2` of posets in `A_4 ⊂ PPF_5`). Its boundary is verified to vanish (a genuine 2-cycle). The second summand's generator is `z_U := z_D` with every relation `(a,b)` reversed to `(b,a)` — the image under the S₄-equivariant order-reversal isomorphism `D ≅ U`, landing in `Δ(U)`.

> **`{ z_D, z_U }`** is an explicit 2-element basis of `B_4`, in a form directly usable by F15 / (E2): the explicit triangle terms are printed by the script (`scripts/compat_geom_cofiber_morse_n4n5.py`, section "explicit basis of B_4"), and the reduction dictionary `H̃_3(Δ_5/Δ_4) ← 2·H̃_2(Δ(A_4))` is §1.2 above.

(The basis is given at the `Δ(D)/Δ(U)` level rather than unwound all the way to literal relative 3-cells of `C_*(Δ_5,Δ_4)`; that is sufficient for (E2) — `∂_3` is the triple connecting homomorphism, and the reduction §1.2 is the explicit dictionary from the `Δ(A_4)` model back to the cofiber. Cf. the AMBER-tag note in the ticket: "delivers B_4 + basis if the cohomology is extractable" — here it is extracted explicitly.)

---

## 3. Trip-wire and cross-checks

### 3.1 Trip-wire: n=3→4 reproduces mg-6295's GREEN

The **identical** reduction pipeline is run for n=3→4 *before* the n=4→5 target. It must reproduce mg-6295 (PCR-Lit-2):

```
MoveA peel elt 3:  |R| = 182, |Q_∅| = 14, 18 distinct fibres all contractible
MoveB:             ideal S, |S| = 14, 2 components of size 7
PEEL kill_up_3/kill_down_3:  |P^{(j)}| = 96 → |A_3| = 66,  Δ(A_3) has 1008 cells
H̃_*(Δ(A_3)) = (0,1,0,0)   (A_3 ≃ S¹)
=> H̃_*(Δ_4/Δ_3) = (0,0,2,0),  χ^{S_3}(cofiber) = 2·sgn_{S_3}
```

**Trip-wire PASS** — `(0,0,2,0) = 2·sgn_{S_3}` is exactly mg-6295's GREEN-constructive-cofiber-Morse result. The reduction machinery is validated against an independently-known answer.

### 3.2 Collapse-engine self-test

The n=3→4 trip-wire keeps every direct computation under the 600 k-cell threshold and so never exercises the elementary-collapse code path. The script therefore separately cross-checks `direct_reduced_homology_big` (collapse + residual Gaussian) against the plain materialised `reduced_betti` (full mod-p Gaussian) on four medium subposets (`PPF_4`; a `D_3`-type poset; `A_4 ∩ {Up_3=0}`; `A_4 ∩ {Down_3=0}`). All four agree — the collapse engine is sound on cases where the direct Gaussian is also feasible.

### 3.3 Independent cross-checks of the n=4→5 result

- **Euler characteristic, three ways.** χ̃(Δ(A_4)) = +1 from the f-vector; from the collapsed residual `(195,606,413)`; and from the equivariant Euler char `χ^{S_4}(Δ(A_4)) = sgn` (dimension 1). All agree. χ̃(Δ_5/Δ_4) = −2 from the f-vector matches `0−0+0−2+0`.
- **The `2·H̃_{*-1}(A_4)` relation.** Computed independently: `H̃_*(Δ(A_4)) = (0,0,1)` and `H̃_*(Δ_5/Δ_4) = (0,0,0,2)` satisfy `H̃_d(cofiber) = 2·H̃_{d-1}(Δ(A_4))` in every degree.
- **The cofiber long exact sequence.** Independently of this computation, the LES of the pair `(Δ_5, Δ_4)` with the established facts `H̃_*(Δ_4) = sgn_{S_4}` in degree 2 and `H̃_*(Δ_5) = sgn_{S_5}` in degree 3 (Hyp(4), Hyp(5), F10 invariants) gives `0 → sgn_{S_5} → B_4 → sgn_{S_4} → 0`, forcing `B_4 = 2·sgn_{S_4}` as an S₄-representation and concentration in degree 3. F14's *direct* cofiber computation agrees — and, being a direct computation of `C_*(Δ_5,Δ_4)`, it is capable of *refuting* the prediction (the RED branch), which the LES restatement is not.

---

## 4. What F14 establishes and does not establish

### 4.1 Establishes

- `b̃_*(Δ_5/Δ_4) = (0,0,0,2,0)`, concentrated in degree 3 — **computed**, not predicted.
- `B_4 = H̃³(Δ_5/Δ_4) = 2·sgn_{S_4}` — **(UCC.1) at level 4 verified by direct computation.**
- An explicit 2-element basis `{z_D, z_U}` of B₄, with the explicit reduction dictionary to the cofiber model — deliverable 3, needed for F15 / (E2).
- A memory-efficient, S_n-equivariant, fully run-time-verified reduction that collapses the 3.3 × 10⁸-cell relative complex `C_*(Δ_5,Δ_4)` onto `2·Δ(A_4)` (1.5 × 10⁷ cells) — the discrete-Morse / cluster-lemma route the ticket asks for, in place of the infeasible naive greedy+Forman enumeration.
- The same pipeline reproduces mg-6295's GREEN at n=3→4 (trip-wire) and passes a collapse-engine self-test.

### 4.2 Does NOT establish

- **`∂_3` is not computed here** — that is F15 / (E2). F14 supplies its codomain `B_4` + an explicit basis; computing the 2×2 matrix `∂_3 : B_3 → B_4` and testing isomorphism is the gated follow-up.
- **No claim about n ≥ 5→6.** F14 is the n=4→5 datapoint of the route-(ii) mechanism; perfection / concentration at higher n is still open (F10 §3.3). What F14 *does* show is that the reduction *mechanism* (MoveA/MoveB/PEEL) is itself n-uniform — it ran identically at n=3→4 and n=4→5 — but each level's collapse hypotheses are re-verified computationally, not assumed.
- **No literal greedy+Forman matching on `C_*(Δ_5,Δ_4)`.** That is infeasible at 3.3 × 10⁸ cells; F14 substitutes the equivalent, memory-efficient cluster-lemma reduction (discrete Morse theory: the cluster lemma assembles fibrewise acyclic matchings into a global acyclic matching). The terminal `Δ(A_4)` *is* reduced by an explicit elementary collapse (a discrete Morse collapse).
- **No new axioms; no Lean changes.** Pure-Python computation + Markdown. The in-tree Lean 4-axiom trust surface is untouched.

---

## 5. Verdict

**GREEN-cofiber-perfect.**

`b̃_*(Δ_5/Δ_4) = (0,0,0,2,0)` concentrated in degree 3, `B_4 = 2·sgn_{S_4}`. (UCC.1) is **computed** (not merely predicted) at n=4→5; an explicit 2-element basis of `B_4` is delivered; the memory-efficient S_n-equivariant order-ideal reduction collapses the 3.3 × 10⁸-cell relative complex onto `2·Δ(A_4)` and reproduces mg-6295's GREEN at n=3→4 (trip-wire) and passes the collapse self-test. **F15 / entry sub-problem (E2) is unblocked.**

---

## 6. References

### 6.1 Predecessor mg-tickets

- **mg-b352** — F11: attack on (FG-Cofiber). `docs/state-F11.md`. §4.6 (E2 gated on PCR-Lit-2′), §6.2 (follow-up B). The triple connecting map `∂_n : B_n → B_{n+1}`; (UCC.1) rep-type half ⟺ `∂_n` iso.
- **mg-6295** — PCR-Lit-2 / M1: Hersh–Welker discrete-Morse on the cofiber. `scripts/compat_geom_cofiber_morse_n3n4.py`, `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md`. The n=3→4 recipe F14 adapts; §6.3 designates "re-run the recipe on `C_*(Δ_5,Δ_4)`" as PCR-Lit-2′; the trip-wire target `(0,0,2,0) = 2·sgn_{S_3}`.
- **mg-8216** — F10: general-n unified proof synthesis. `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. §1.1 (`|PPF_n|`), §3.3 (perfection n-dependent), §10.2 (M1+M2 consistency prediction `(0,0,0,2,0)`).
- **mg-f91f / mg-59f3** — PCR-1 / PCR-2: the n=3→4 cofiber, relative Betti `(0,0,2,0)`, `m_{X/A}^sgn = 2`.

### 6.2 Mathematical literature

- P. Hersh, *On optimizing discrete Morse functions*, Adv. Appl. Math. 35 (2005) — the cluster lemma.
- J. Jonsson, *Simplicial complexes of graphs*, LNM 1928 (2008) — the patchwork theorem (fibrewise acyclic matchings assemble).
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — discrete Morse theory; elementary collapse.
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11 — discrete Morse theory for subcomplex pairs; order-ideal filtrations.

### 6.3 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration.
- 2026-05-14T08:05Z — focus on the induction, not special cases. (F14 is the *gating computation* for the general-n route (ii) mechanism, the prerequisite to test the iso hypothesis the whole route hinges on — not a fixed-n datapoint hunt.)

---

*Polecat: mg-3839 (F14). Branch: `compat-geom-F14-B4-cofiber-cohomology`. Verdict: **GREEN-cofiber-perfect** — `b̃_*(Δ_5/Δ_4) = (0,0,0,2,0)`, `B_4 = H̃³(Δ_5/Δ_4) = 2·sgn_{S_4}`, computed (not predicted) via a memory-efficient S_n-equivariant order-ideal-filtration reduction of the 3.3×10⁸-cell relative complex; explicit 2-element basis delivered; n=3→4 trip-wire reproduces mg-6295's GREEN. No new axioms; no Lean changes. F15/(E2) unblocked.*
