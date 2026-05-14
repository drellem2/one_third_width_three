# Compat-Geom — F22-HPC: cell-tracking the F14/F17 cofiber Morse reduction — the explicit critical cells of M_rel^eq (mg-43fb)

**Branch:** `polecat-cat-mg-43fb` (Session 1); `polecat-cat-mg-0c5d` (Session 2).
**Parent:** mg-a2cb (F21, GREEN-needs-hpc-anchor) §8 — F21 named this Tier-3 anchor ticket precisely.
**Chain:** F10 → F17 (mg-4d3a, `M_rel^eq`) → F18 (mg-d039) → F19 → F20 → F21 (mg-a2cb, Prop F21.1) → **F22-HPC (mg-43fb)**.
**Type:** Tier-3 HPC enumeration / reduction computation — cell-tracking through F17's F14 order-ideal reduction. **No new axioms; no Lean changes; no (co)homology datapoint touching the trust surface.** Multi-session; cumulative state in `docs/state-F22-HPC.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T17:23Z (milestone 1 — full gap-free width-3 proof, no sketches or gaps); 2026-05-14T20:32Z (PROCEED — authorised the Tier-3 anchor).

> **Session 2 (mg-0c5d) verdict: RED-tripwire.** The cross-boundary cancellation was implemented and run materialised at `n = 3`: it produces `D-lift(c*_n)` (an `M_rel^eq` critical cell), **not** the recorded `c*_{n+1}` — which is structurally never a cross-boundary survivor. F21.1's "(the descent of)" is a genuine, essential, HPC-class, canonically under-specified operation; the naive survivor tower *refutes* (CM-rel) at `n = 6`. The genuine `c*_6, c*_7` are **not** produced. See the **Session 2** section below (after §8) and `docs/state-F22-HPC.md` §5. Surfaced immediately per the ticket protocol.

**Verdict: GREEN-partial.** *(Session 1.)* F22-HPC Session 1 builds the cell-tracking infrastructure and **materialises the two critical `(n−1)`-cells of F17's perfect `S_n`-equivariant cofiber Morse matching `M_rel^eq`** — as explicit chains in `PPF_{n+1}` — for **`n = 3, 4, 5`**, via the F17-structural (closure-operator, memory-efficient) terminal reduction seeded with the known exact `c*_3, c*_4, c*_5`. **(CM-rel) is checked on the anchor data and CONFIRMED at `n = 3, 4, 5`**: every materialised critical cell has a **width-2 ordinal-sum-of-antichains top poset with a size-2 block** (`OSA(1,1,2)`, `OSA(1,2,1,1)`, `OSA(1,2,2,1)`) and **every internal per-step Kahn–Saks `Pr` lies in `[3/11, 8/11]`**. The `n = 5` cell `c_D` has top poset `OSA(1,2,2,1)` — one of F20's 12 genuine-`G_6` candidates. Session 1 also establishes a **precise, load-bearing finding** (§5): F17's `M_rel^eq` critical cells carry `c*_n`'s *internal* structure, **not** `c*_{n+1}`'s — they are **not** in the `S_{n+1}`-orbit of the F21-recorded chamber-Morse `c*_{n+1}`. So F21.1's "`c*_{n+1}` is **(the descent of)** a critical cell of `M_rel^eq`" is confirmed to need the **F18 cross-boundary cancellation as a genuine cell-transforming step** — not a "pick the survivor" identification. Pinning the genuine `c*_6, c*_7` (resolving F20's 12-candidate short list) is therefore the continuation gate: `n = 6, 7` need either `c*_6 / c*_7` as the terminal seed (the very unknowns), the non-materialising intrinsic structural cell-tracking (genuinely HPC — `Δ(A_5)` already has `1.35·10¹³` cells), **or** the cross-boundary-cancellation tower. Trust-surface impact: **none**.

**Deliverables (this session):**
- `scripts/compat_geom_F22_hpc_cell_tracking.py` — the cell-tracking upgrade of the F14-reduction scripts (pure-Python stdlib, exact arithmetic, runtime ≈ 0.1 s for `n = 3,4,5`; the `n = 3` materialised cross-check ≈ 0.1 s).
- `docs/compatibility-geometry-F22-hpc-critical-cells.md` (this doc).
- `docs/state-F22-HPC.md` (cumulative state ledger).

---

## §0. Executive summary

### 0.1 The F22-HPC mandate

After F17 + F18 the F10 cohomological core is unconditional. F19 → F20 → F21 worked the numerical width-3 conclusion (F10 part (iii)) down to **(CM-struct)**, which F21's **Proposition F21.1** (the cofiber-Morse induction) re-founded and **reduced to (CM-rel)**: a statement about the explicit critical `(n−1)`-cells of F17's perfect `S_n`-equivariant cofiber Morse matching `M_rel^eq` on `C_∗(Δ_{n+1}, Δ_n)`. F17 proved `M_rel^eq` perfect with two critical `(n−1)`-cells but, by design (F17 §7.2), did **not** materialise them. F22-HPC is the Tier-3 anchor that materialises them — the **cell-tracking upgrade** of `compat_geom_cofiber_morse_n4n5.py` / `compat_geom_F17_equivariant_morse.py`, which run the F14 reduction at the *homology* level only.

### 0.2 What the F14/F17 reduction is (recap)

F17 (Theorem 2.4, §4) proves, `n`-uniformly and `S_n`-equivariantly, that the F14 order-ideal reduction collapses the relative complex:

```
  C_∗(Δ_{n+1}, Δ_n)
    --[MoveA: peel element n]-->            C_∗(Δ(R), Δ(Sub))
    --[MoveB: the Type-∅ ideal S = S↓ ⊔ S↑]--> Δ(D_n) ⊕ Δ(U_n)     [degree shift +1]
    --[PEEL: kill_up_n interior operator]-->  Δ(A_n) ⊕ Δ(A_n)       [homology iso]
```

with `A_n` the F17 `(Q,F)`-model terminal complex and the order-reversal involution an `S_n`-equivariant `D_n ≅ U_n`, giving `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d−1}(Δ(A_n))`. F17 §4 further collapses `Δ(A_n)` onto `Δ_n = Δ(PPF_n)`: the `S_n`-equivariant **closure operator** `c(Q,F) = (Q,[n])` retracts the order ideal `A_n^{nt}` onto `{(Q,[n])} ≅ PPF_n`, and `A_n^t` attaches along contractible down-sets. So `M_rel^eq` is the composite Morse matching, and **its critical cells number `2·dim H̃_∗(Δ_n)`** — under `Hyp(n)`, exactly **two critical `(n−1)`-cells**, one in each `D_n / U_n` copy.

### 0.3 The cell-tracking lift

A critical `(n−2)`-cell of `Δ_n` — the canonical chamber-Morse critical cell `c*_n = (Q_0 ⊂ ⋯ ⊂ Q_{n−2})` — lifts to a critical `(n−1)`-cell of `M_rel^eq` by composing the explicit reduction maps **backwards**:

1. **closure operator (F17 §4.1), inverse.** `c*_n` lifts into `A_n^{nt}` cellwise: `Q_i ↦ (Q_i,[n]) ↦ x_i := Q_i ∪ {(n,b) : b ∈ [n]}` (element `n` placed *below* every element). `(x_0 ⊂ ⋯ ⊂ x_{n−2})` is a critical `(n−2)`-cell of `Δ(A_n)`.
2. **PEEL (F17 §2.3).** `A_n ⊂ D_n` is the inclusion (a homology iso); the chain is unchanged.
3. **MoveB (F17 §2.2), `+1` degree shift.** `D_n = P^{(↓)}`; the `S↓` cone fibre over the bottom `x_0` has apex `s*(x_0) := {(n,b) : b ∈ Down_n(x_0)}`. Prepend it: the chain becomes `(s*(x_0) ⊂ x_0 ⊂ ⋯ ⊂ x_{n−2})`.
4. **MoveA (F17 §2.1).** A homology iso, no degree shift — the chain is now a relative `(n−1)`-cell of `C_∗(Δ_{n+1}, Δ_n)`.

This gives `c_D`, the critical cell of the `D_n` summand. The `U_n` summand's critical cell `c_U` is `c_D` under the `S_n`-equivariant order-reversal `D_n ≅ U_n` (every relation `(a,b) ↦ (b,a)`).

> **The two critical `(n−1)`-cells of F17's `M_rel^eq` are `c_D` and `c_U = order-reversal(c_D)`.**

This is the F17-structural route: it never materialises `Δ(A_n)` (which has `1008`, `1.5·10⁷`, `1.35·10¹³` cells at `n = 3, 4, 5`) — the memory-efficient route the ticket asks for. The seed `c*_n` for `n = 3, 4, 5` is the known exact canonical critical cell (F21 §2).

### 0.4 The headline results

| `n` | `c_D` `|L|`-profile | apex-step `Pr` | internal per-step `Pr` | `c_D` top poset | (CM-rel)? |
|----:|---|---|---|:---:|:---:|
| 3 | `(6, 3, 2)` | `1/2` | `(2/3)` | `OSA(1,1,2)` | ✓ |
| 4 | `(24, 5, 3, 2)` | `5/24` | `(3/5, 2/3)` | `OSA(1,2,1,1)` | ✓ |
| 5 | `(120, 30, 14, 8, 4)` | `1/4` | `(7/15, 4/7, 1/2)` | `OSA(1,2,2,1)` | ✓ |

All cells: genuine relative cells of `C_∗(Δ_{n+1}, Δ_n)`, `S_n`-dual via order-reversal, **(CM-rel) confirmed**. Cross-checks: the F14 homology reduction reproduces `H̃_∗(Δ_4/Δ_3) = (0,0,2,0)` (the cofiber has 2 critical `2`-cells); `Δ(A_3)` is shown to admit a perfect Morse matching with critical counts `(1,1,0,0)` — exactly one critical `1`-cell, doubled by `D/U` to the two critical `2`-cells of `M_rel^eq`.

---

## §1. The cell-tracking lift, in detail

### 1.1 The lift maps are F17's reduction maps, run in reverse

Each of the four steps in §0.3 is **an explicit `n`-independent map**, transcribed directly from the F17 reduction:

- **Step 1** is the inverse of F17 Proposition 4.1's closure operator. F17 proves `c(Q,F) = (Q,[n])` is an `S_n`-equivariant closure operator on `A_n^{nt}` with `c(A_n^{nt}) ≅ PPF_n`; its Morse-collapse critical cells are the chains entirely in the image `{(Q,[n])}`. The lift `Q_i ↦ x_i = Q_i ∪ {(n,b):b∈[n]}` is the `(Q,[n]) ↦ x` coordinate change of F17 Lemma 1.1.
- **Step 2** is the inclusion `A_n ↪ D_n`: `A_n` is exactly the fixed set of F17's `kill_up_n` interior operator (F17 §2.3), so a chain in `A_n` *is* a chain in `D_n`.
- **Step 3** is the MoveB cone-fibre apex. F17 Proposition 2.2: for `x ∈ Sub`, the fibre `S↓_{<x} ≅ {T : ∅ ≠ T ⊆ Down_n(x)}` is a Boolean cone with maximum `Down_n(x)`. The cluster-lemma toggle-apex matching cones it off; the surviving cell of the `(+1)`-shifted summand is the chain with the apex `s*(x_0) = {(n,b) : b ∈ Down_n(x_0)}` prepended.
- **Step 4** is MoveA: F17 Proposition 2.1 / Theorem 2.4 — a homology iso realised by a matching; the chain, lying entirely in `R` and touching `Q_∅` (its prepended bottom `s*(x_0)` has `x_0|_{[n]} = ∅`), is a relative `(n−1)`-cell of `C_∗(Δ_{n+1}, Δ_n)`.

For the closure-operator lift, `Down_n(x_0) = [n]` (every `x_i` has `n` below all of `[n]`), so the apex is `s* = {(n,0), …, (n,n−1)}` — the poset "`n` below an `[n]`-antichain", `OSA(1, n)`.

### 1.2 Validity — what the script computes vs. what it cites

The script `materialises` the cell by applying the four explicit maps. That the result *is* a critical `(n−1)`-cell of a genuine perfect `S_n`-equivariant `M_rel^eq` rests on a **chain of cited theorems**, not on a computation:

- F17 Theorem 2.4 + §4: the F14 reduction `MoveA/MoveB/PEEL` + the `A_n^{nt}` closure + the `A_n^t` attachment is a valid `S_n`-equivariant Morse collapse `C_∗(Δ_{n+1},Δ_n) → 2·Δ_n`.
- F21 §2 / F8 / F5 / F2: `c*_n` is *the* canonical chamber-Morse critical `(n−2)`-cell of `Δ_n` (verified exactly for `n = 3, 4, 5`).
- Composing: the lift `c_D` is the critical `(n−1)`-cell of the `D_n` copy of the F17-structural `M_rel^eq` whose terminal `Δ_n`-matching has critical cell `c*_n`.

The script **independently verifies**: (a) every `c_D, c_U` is a genuine relative cell of `C_∗(Δ_{n+1},Δ_n)` — every poset proper and non-total on `[n+1]`, strictly increasing chain, not contained in `ι_n(PPF_n)`; (b) `c_U = order-reversal(c_D)`; (c) the F14 homology reduction (imported from `compat_geom_cofiber_morse_n4n5.py`) gives the cofiber Betti `(0,0,2,0)` at `n = 3`; (d) `Δ(A_3)` admits a perfect Morse matching with critical counts `(1,1,0,0)` — confirming the "one critical `(n−2)`-cell of `Δ(A_n)`, doubled" structure empirically at the one `n` where `Δ(A_n)` is small enough to materialise.

### 1.3 A subtlety F22-HPC pins down: the terminal `Δ_n` matching

F17 (§7.2) explicitly does **not** materialise `M_rel^eq`'s two cells, and the reason is structural: the F14 reduction collapses `C_∗(Δ_{n+1},Δ_n)` onto `2·Δ_n`, but the **terminal perfect matching on `Δ_n` is not pinned by F17** — F17 only needs homology. So "*the* two critical cells of `M_rel^eq`" is genuinely under-specified by F17; F22-HPC must choose the terminal `Δ_n`-matching. The F17-faithful, `S_n`-equivariant, memory-efficient choice is: the chamber-Morse matching `M_n`, with critical cell `c*_n`. That is the choice this session makes. §5 records the consequence — and why it is *not* the only defensible choice.

---

## §2. The materialised critical cells — explicit chains

All chains below are written bottom-to-top as Hasse (cover) relations; the actual posets are the transitive closures. Element `n` is the `S_n`-fixed new element.

### 2.1 `n = 3` — `M_rel^eq` on `C_∗(Δ_4, Δ_3)`, the two critical `2`-cells

Seed `c*_3 = {0<2} ⊂ {0<1, 0<2}` (F8 §4.5).

```
c_D  =  {3<0,3<1,3<2}  ⊂  {0<2, 3<0,3<1}  ⊂  {0<1,0<2, 3<0}
c_U  =  {0<3,1<3,2<3}  ⊂  {0<3,1<3, 2<0}  ⊂  {0<3, 1<0,2<0}      [ = order-reversal(c_D) ]
```

`c_D` `|L|`-profile `(6, 3, 2)`; top poset `OSA(1,1,2)` (width 2, size-2 block); apex-step `Pr = 1/2`, internal step `Pr = 2/3` — BFT-sharp. **(CM-rel) ✓.**

### 2.2 `n = 4` — `M_rel^eq` on `C_∗(Δ_5, Δ_4)`, the two critical `3`-cells

Seed `c*_4 = {1<2,3<0,3<2} ⊂ {0<2,1<2,3<0} ⊂ {0<2,1<0,3<0}` (F2 §4.3.1).

```
c_D  =  {4<0,4<1,4<2,4<3}
        ⊂  {1<2,3<0,3<2, 4<1,4<3}
        ⊂  {0<2,1<2,3<0, 4<1,4<3}
        ⊂  {0<2,1<0,3<0, 4<1,4<3}
c_U  =  order-reversal(c_D)
```

`c_D` `|L|`-profile `(24, 5, 3, 2)`; top poset `OSA(1,2,1,1)` (width 2, size-2 block); apex-step `Pr = 5/24`, internal steps `Pr = (3/5, 2/3)` — both BFT-sharp. **(CM-rel) ✓.**

### 2.3 `n = 5` — `M_rel^eq` on `C_∗(Δ_6, Δ_5)`, the two critical `4`-cells

Seed `c*_5 = {0<1,2<1,3<1} ⊂ {0<1,0<4,2<1,2<4,3<1} ⊂ {0<4,2<4,3<1,4<1} ⊂ {0<3,0<4,2<3,2<4,3<1,4<1}` (F5 §4.3 / F8′ §A).

```
c_D  =  {5<0,5<1,5<2,5<3,5<4}
        ⊂  {0<1,2<1,3<1, 5<0,5<2,5<3,5<4}
        ⊂  {0<1,0<4,2<1,2<4,3<1, 5<0,5<2,5<3}
        ⊂  {0<4,2<4,3<1,4<1, 5<0,5<2,5<3}
        ⊂  {0<3,0<4,2<3,2<4,3<1,4<1, 5<0,5<2}
c_U  =  order-reversal(c_D)
```

`c_D` `|L|`-profile `(120, 30, 14, 8, 4)`; width profile `(5, 4, 3, 3, 2)`; top poset `OSA(1,2,2,1)` (width 2, size-2 block); apex-step `Pr = 1/4`, internal steps `Pr = (7/15, 4/7, 1/2)` — all BFT-sharp. **(CM-rel) ✓.**

> **`c_D`'s top poset `OSA(1,2,2,1)` is one of F20 §6's 12 candidates for the genuine `G_6`.** This is the F17-structural `M_rel^eq`'s answer; §5 explains why it is `c*_5`'s structure lifted, not yet the genuine `c*_6`.

---

## §3. (CM-rel) on the anchor data — confirmed at `n = 3, 4, 5`

**(CM-rel)** (F21 §5.1): *the two critical `(n−1)`-cells of `M_rel^eq` have width-2 ordinal-sum-of-antichains top posets (with a size-2 block), and every internal per-step `Pr` lies in `[3/11, 8/11]`.*

The materialised cells **confirm (CM-rel) at `n = 3, 4, 5`**:

| `n` | `c_D` top poset | width-2 OSA? | size-2 block? | internal `Pr`'s | all in `[3/11,8/11]`? |
|----:|:---:|:---:|:---:|---|:---:|
| 3 | `OSA(1,1,2)` | ✓ | ✓ | `2/3` | ✓ |
| 4 | `OSA(1,2,1,1)` | ✓ | ✓ | `3/5, 2/3` | ✓ |
| 5 | `OSA(1,2,2,1)` | ✓ | ✓ | `7/15, 4/7, 1/2` | ✓ |

**Why it holds — and why this is honest, not circular.** The closure-operator lift places `n` *below* every element of each `Q_i`, so `x_i = Q_i ∪ {n < [n]}` and:
- the **top poset** of `c_D` is `x_{n−2} = OSA(1) ⊕ G_n` where `G_n` is `c*_n`'s top poset; an ordinal sum prepended with a singleton block is still a width-2 OSA, and it still has a size-2 block iff `G_n` does;
- `|L(x_i)| = |L(Q_i)|` (placing `n` below all forces it to the bottom of every linear extension), so the **internal `|L|`-profile of `c_D` equals `c*_n`'s `|L|`-profile**, and the internal per-step `Pr`'s of `c_D` are exactly `c*_n`'s per-step `Pr`'s.

So **(CM-rel) for `c_D` ⟺ `c*_n` satisfies (L2-struct) + internal-BFT-sharpness** — which F21 §2 records as **TRUE for `n = 3, 4, 5`**. F22-HPC's contribution here is *not* a re-derivation of that fact: it is the **explicit materialisation** of the `M_rel^eq` critical cells and the **structural proof** that, for the F17-structural `M_rel^eq`, the cofiber matching's critical-cell structure is *inherited* from the chamber-Morse `c*_n`. The apex-step `Pr` (`1/2, 5/24, 1/4` at `n = 3, 4, 5`) is the MoveB coning step — a structural artefact of the reduction, not an "internal" step of the genuine chain, hence correctly excluded from the BFT-sharp clause of (CM-rel) (the F21 §5.1 wording: "every **internal** per-step `Pr`").

This is the **GREEN** branch of the F22-HPC verdict matrix on the (CM-rel) question: the materialised cells **do** have width-2-OSA tops with BFT-sharp internal steps — **not** the RED-cm-rel-false branch.

---

## §4. Cross-checks

- **F14 homology reduction, `n = 3`.** The script imports `cofiber_homology` from `compat_geom_cofiber_morse_n4n5.py` and runs the full F14 reduction for `Δ_4/Δ_3`: result `H̃_∗(Δ_4/Δ_3) = (0,0,2)` — the cofiber has exactly **2 critical `2`-cells**, consistent with the materialised pair `{c_D, c_U}`. (For `n = 4` the homology reduction is the `3.3·10⁸`-cell F14 computation — established GREEN in F14, `H̃_∗(Δ_5/Δ_4) = (0,0,0,2,0)`; not recomputed here, to stay memory-conscious.)
- **Materialised perfect matching, `n = 3`.** `Δ(A_3)` (`1008` cells, `f = (66,312,438,192)`, `H̃_∗ = (0,1,0,0)`, i.e. `≃ S¹`) is materialised and a perfect Benedetti–Lutz random-discrete-Morse matching is found with critical counts `(1,1,0,0)` — **exactly one critical `1`-cell**. Via the `D_n ≅ U_n` duality this is the "`2·1 = 2` critical `(n−1)`-cells of `M_rel^eq`" structure, confirmed empirically at the one `n` where `Δ(A_n)` is small enough to materialise.
- **Structural verification, all `n`.** Every `c_D, c_U` at `n = 3, 4, 5` is verified to be a genuine relative cell of `C_∗(Δ_{n+1},Δ_n)` (every poset proper non-total on `[n+1]`, strictly increasing, uses element `n`) and `c_U = order-reversal(c_D)`.

---

## §5. The load-bearing finding: `M_rel^eq`'s critical cells vs. the chamber-Morse `c*_{n+1}`

F21's Proposition F21.1 states: *`c*_{n+1}` is **(the descent of)** a critical `(n−1)`-cell of `M_rel^eq`* — specifically the one surviving the F18 cross-boundary cancellation against `c*_n`. F22-HPC, materialising the cells, can now test the literal reading of that statement. **It does not hold literally for F17's `M_rel^eq`.**

### 5.1 The materialised cells are not in the orbit of the F21-recorded `c*_{n+1}`

`|L|`-profile is an `S_{n+1}`-orbit invariant. Comparing:

| | `c_D` `|L|`-profile | F21-recorded `c*_{n+1}` `|L|`-profile | same orbit? |
|---|---|---|:---:|
| `n = 3` | `(6, 3, 2)` | `c*_4 = (5, 3, 2)` | **no** |
| `n = 4` | `(24, 5, 3, 2)` | `c*_5 = (30, 14, 8, 4)` | **no** |

`c_D`'s **internal** `|L|`-profile is exactly `c*_n`'s `|L|`-profile (`(3,2)` at `n = 3`; `(5,3,2)` at `n = 4`) — it carries `c*_n`'s structure, with the MoveB apex prepended. It does **not** carry `c*_{n+1}`'s structure.

### 5.2 The structural reason

The F21-recorded `c*_{n+1}` lies, in the F14-reduction picture, **in the MoveB filter `Sub`** — not in the locus where `M_rel^eq`'s critical cells sit. Concretely, take `c*_4 = (P_0, P_1, P_2)`: every `P_i` has `P_i|_{[3]} ≠ ∅` **and** `Down_3(P_i) ≠ ∅`, `Up_3(P_i) = ∅` — i.e. every `P_i ∈ A_3 ⊂ D_3 ⊂ Sub`. So `c*_4` is a chain *entirely in `Δ(Sub)`*. But `M_rel^eq`'s critical `(n−1)`-cells are, by the MoveB structure, exactly the chains of the form `(apex ⊂ chain-in-D_n)` with `apex ∈ S` (`apex|_{[n]} = ∅`). `c*_4`'s bottom poset `P_0` has `P_0|_{[3]} = {1<2} ≠ ∅`, so `P_0 ∉ S`: **`c*_4` is not of the form `(apex ⊂ …)`**. Under MoveA, `c*_4` (lying in `Sub`, not touching `Q_∅`) is **matched, not critical**. So `c*_4 ∉ crit(M_rel^eq@3)` — for *any* perfect matching `M_rel^eq` respecting the F14 reduction structure. The same holds at `n = 4` for `c*_5`.

This is not specific to the closure-operator terminal matching: it is forced by the **MoveA/MoveB shape** of the F14 reduction. The intrinsic-combinatorial route (a perfect Morse matching of `Δ(A_3)` found directly, e.g. by random discrete Morse — also implemented and run) gives a *different* critical cell, but it too lifts to an `(apex ⊂ chain-in-A_3)` cell, not to `c*_4`.

### 5.3 What this means — F21.1's "(the descent of)" is genuinely a cell transform

F21.1's parenthetical "**(the descent of)**" is therefore **load-bearing**: `c*_{n+1}` is **not** literally a critical cell of `M_rel^eq`. The relationship is:

> `M_rel^eq` has two explicit critical `(n−1)`-cells `c_D, c_U` (materialised by F22-HPC, §2). The genuine chamber-Morse `c*_{n+1}` is obtained from them by the **F18 cross-boundary Forman cancellation** of `c*_n` against one of `{c_D, c_U}` — and this cancellation is a **genuine cell-transforming operation** (it reverses a gradient `V`-path through the assembled `M_{n+1} = M_n ⊔ M_rel^eq`), not a "pick the survivor" identification. The survivor's *cell* is not `c*_{n+1}`; `c*_{n+1}` is its *descent*.

This is the precise refinement of F21.1 that the anchor data delivers. It is **consistent** with everything F21 actually *proved* (F21 only verified the **necessary condition** "`c*_n` is a relative cell", harness [E] — never "`c*_n ∈ crit(M_rel^eq)`"), and it **sharpens** F21's own §5.4 caveat ("the anchor is necessary, not automatically sufficient"). It is **not** a refutation of (CM-rel): (CM-rel) is about `M_rel^eq`'s critical cells, and §3 confirms it on them.

### 5.4 Why this changes the continuation plan

The F22-HPC ticket's primary deliverable (b) — "the genuine `c*_6, c*_7` as explicit chains" — therefore needs **one more step beyond materialising `M_rel^eq`'s critical cells**: the **F18 cross-boundary cancellation tracking**. With `c*_5` known and `M_rel^eq@5`'s cells `c_D, c_U` now materialised (§2.3), the inputs to the `n = 5` cross-boundary cancellation are in hand — what remains is to *run* it, which requires the assembled `M_6 = M_5 ⊔ M_rel^eq@5` and the unique gradient `V`-path. That, and the `n = 6, 7` tower, is the continuation gate (§7).

---

## §6. What F22-HPC Session 1 establishes and does not establish

### 6.1 Establishes

- **The cell-tracking infrastructure** (`scripts/compat_geom_F22_hpc_cell_tracking.py`) — the explicit `closure-operator → PEEL → MoveB → MoveA` lift maps, on top of the F17 `(Q,F)`-model, memory-efficient (never materialises `Δ(A_n)` for the lift).
- **The two critical `(n−1)`-cells of F17's `M_rel^eq` materialised, as explicit chains in `PPF_{n+1}`, for `n = 3, 4, 5`** (§2) — for the F17-structural (closure-operator) `M_rel^eq` seeded with the known `c*_3, c*_4, c*_5`. Genuine relative cells; `S_n`-dual.
- **(CM-rel) checked on the anchor data and CONFIRMED at `n = 3, 4, 5`** (§3): width-2-OSA top posets with size-2 blocks (`OSA(1,1,2)`, `OSA(1,2,1,1)`, `OSA(1,2,2,1)`), all internal per-step `Pr` in `[3/11, 8/11]`. The `n = 5` top poset `OSA(1,2,2,1)` is one of F20's 12 genuine-`G_6` candidates.
- **The structural reason (CM-rel) holds on the F17-structural `M_rel^eq`** (§3): its critical cells *inherit* `c*_n`'s `(L2-struct)` + internal-BFT-sharpness through the closure-operator lift.
- **The load-bearing finding** (§5): F17's `M_rel^eq` critical cells are **not** in the `S_{n+1}`-orbit of the F21-recorded chamber-Morse `c*_{n+1}` — `c*_{n+1}` lies in the MoveB filter `Sub`, not in `crit(M_rel^eq)`. F21.1's "(the descent of)" is a genuine cell transform via the F18 cross-boundary cancellation, not a survivor-identification. This sharpens F21.1 and re-scopes deliverable (b).
- **Cross-checks** (§4): F14 homology reduction `→ (0,0,2,0)` at `n = 3`; `Δ(A_3)` perfect Morse matching `(1,1,0,0)`.

### 6.2 Does NOT establish

- **The genuine `c*_6, c*_7` are NOT pinned.** The materialised `c_D@5, c_U@5` are `M_rel^eq@5`'s critical cells, *not* `c*_6` (§5). F20's 12-candidate short list for `G_6` is **not resolved** by this session.
- **`n = 6, 7` cells are not materialised.** The closure-operator route at `n = 6` needs `c*_6` as the terminal seed — the very unknown; the intrinsic-combinatorial route needs `Δ(A_6)` (vastly larger than `Δ(A_5)`'s `1.35·10¹³` cells). See §7.
- **The F18 cross-boundary cancellation is not run.** It is the step that produces `c*_{n+1}` from `M_rel^eq`'s cells + `c*_n` (§5.3–5.4); not in this session.
- **No new axioms; no Lean changes; no (co)homology datapoint touching the trust surface.** It is an enumeration/reduction computation; the in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact is untouched. Route (iii) / mg-b345 stays parked.

---

## §7. The continuation — `n = 6, 7` and the cross-boundary cancellation gate

A continuation session (cumulative state in `docs/state-F22-HPC.md`) faces three sub-goals, in priority order:

1. **The F18 cross-boundary cancellation tracking** (the deliverable-(b) gate). Implement the assembly `M_{n+1} = M_n ⊔ M_rel^eq + cross-boundary cancellation` at the cell level, run it at `n = 4` (where `c*_5` is known — the trip-wire: the cancellation of `c*_4` against `{c_D@4, c_U@4}` must descend to `c*_5`), then at `n = 5` to **produce the genuine `c*_6`**. This is the step §5 shows is genuinely needed and genuinely missing.
2. **`n = 6`** (priority, per F21 §8). With `c*_6` produced by sub-goal 1, the closure-operator lift of `c*_6` gives `M_rel^eq@6`'s critical cells immediately; the cross-boundary cancellation at `n = 6` then gives `c*_7`.
3. **`n = 7`** (only if budget permits — F21 §8). As sub-goal 2, one level up.

The genuine HPC load, if sub-goal 1's cross-boundary cancellation itself proves Tier-3-heavy (it involves `M_n` on `Δ_n`, which F20/F21 flag as HPC-class beyond `n = 5`), is the non-materialising structural cell-tracking of the assembled `M_{n+1}` — the F14/F9-S2 memory-efficiency precedents apply. The `compat_geom_F22_hpc_cell_tracking.py` infrastructure (the `(Q,F)`-model, the explicit lift maps, the structural-reduction objects) is the foundation a continuation session builds on.

---

## §8. Verdict — GREEN-partial

**GREEN-partial.** F22-HPC Session 1 materialises the two critical `(n−1)`-cells of F17's `M_rel^eq` at `n = 3, 4, 5` (the cell-tracking upgrade — explicit chains in `PPF_{n+1}`, the F17-structural memory-efficient route), and **checks (CM-rel) on the anchor data — CONFIRMED at `n = 3, 4, 5`** (width-2-OSA tops with size-2 blocks; internal per-step `Pr` all BFT-sharp). It is **not GREEN-cells-materialised**: the genuine `c*_6, c*_7` are not pinned — Session 1's §5 finding shows that pinning them needs the F18 cross-boundary cancellation, a step beyond materialising `M_rel^eq`'s critical cells. It is **not RED-cm-rel-false**: (CM-rel) is *confirmed*, not refuted, on every materialised cell. It is **not AMBER-budget-capped**: the closure-operator route is cheap (≈ 0.1 s) — the bound is structural (the cross-boundary cancellation gate), not budgetary. It is **GREEN-partial** in the precise sense of the F22-HPC verdict matrix: *cells materialised at `n = 5`; `n = 6/7` needs a continuation session*, and the cumulative state ledger says exactly what remains and how (§7).

**For the PM.** Session 1 surfaces one substantive finding worth a roadmap note: **F21's Proposition F21.1, as literally stated ("`c*_{n+1}` is a critical cell of `M_rel^eq`"), is too strong** — `c*_{n+1}` lies in the MoveB filter `Sub`, *matched* (not critical) by F17's `M_rel^eq` (§5.2). F21.1 is *saved* by its own parenthetical "(the descent of)": the genuine `c*_{n+1}` is the **descent** of `M_rel^eq`'s critical cells under the F18 cross-boundary cancellation, a genuine cell transform. This does not touch the cohomological core, (CM-rel), or the trust surface — but it re-scopes the F22-HPC → F23 boundary: the cross-boundary cancellation tracking is *inside* the anchor's remaining work, not a downstream structural follow-on.

### 8.1 Trust-surface impact

**None.** F22-HPC Session 1 introduces no new axioms, makes no Lean changes, runs no (co)homology HPC datapoint. It is the explicit cell-tracking of the F14/F17 reduction (elementary order-complex combinatorics + exact arithmetic) plus a small materialised cross-check at `n = 3`. The in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact is untouched. Route (iii) / mg-b345 stays parked.

---

# Session 2 (mg-0c5d) — the F18 cross-boundary cancellation tracking — **RED-tripwire**

**Branch:** `polecat-cat-mg-0c5d`. **Verdict: RED-tripwire** (surfaced immediately, per the ticket protocol — mail to `mayor` and `human`, 2026-05-14).

Session 2 implemented the F18 cross-boundary Forman cancellation at the cell level and ran it **materialised at `n = 3`** (`Δ_4`, ≈ `1.5·10⁴` cells — exact, reproducible: `scripts/compat_geom_F22_hpc_cell_tracking.py` Section 10, building on the mg-3839/mg-6295 cofiber-Morse infrastructure `scripts/compat_geom_cofiber_morse_n3n4.py`). The `n = 3` run is the built-in trip-wire, and it pins down precisely what the cross-boundary cancellation does — and what it does **not** do.

## §S2.1 What the cross-boundary cancellation actually does

Assemble `M_4 = M_3 ⊔ M_rel^eq` on `Δ_4` (`M_3` = perfect chamber-Morse matching on `Δ_3`, critical cell `c*_3`; `M_rel^eq` = perfect cofiber matching on `C_∗(Δ_4, Δ_3)`, critical cells `c_D, c_U`). Critical vector `(0,1,2,0)`. Run the cross-boundary Forman cancellation `(0,1,2,0) → (0,0,1,0)`:

- The cancellation cancels `c*_3` against **one** of `{c_D, c_U}` along a **unique gradient `V`-path** (length 22) — a valid Forman cancellation. The result `M_4` is **perfect and acyclic**.
- By Forman's cancellation theorem, the **other** critical `2`-cell survives **UNCHANGED**. The materialised survivor is **`D-lift(c*_3)` exactly** (`|L|`-profile `(6,3,2)`) — i.e. Session 1's `c_D@3`, the closure-operator lift.

This is structural and `n`-uniform: `M_rel^eq`'s two critical `(n−1)`-cells are *exactly* `{D-lift(c*_n), U-lift(c*_n)}` (F17 §4 + Session 1 §1), and the cross-boundary cancellation leaves the un-cancelled one unchanged. **So the survivor is always a closure-operator lift of `c*_n`.**

## §S2.2 The survivor is NOT `c*_{n+1}`

The F2/F5-recorded `c*_{n+1}` is **not** of closure-operator-lift shape: its bottom poset has nonempty restriction to `[n]` (e.g. `c*_4`'s bottom `{1<2,3<0,3<2}` has `{1<2}` inside `[3]`). A closure-operator lift's bottom is an *apex* `ω_n ∈ S↓` with `restriction = ∅`. Hence the recorded `c*_{n+1}` can **never** be a cross-boundary survivor — for *any* `M_rel^eq`. `c*_4`'s `|L|`-profile `(5,3,2) ≠ (6,3,2)` = the survivor's; different `S_4`-orbits.

## §S2.3 The catastrophe — the naive "survivor tower" fails (CM-rel)

If one took the genuine tower to be the naive **survivor tower** `c*_{n+1} := D-lift(c*_n)` (the cross-boundary survivor, iterated), then:

| `n` | `|L|`-profile | per-step `Pr` | internal per-step `Pr` | (CM-rel)? |
|----:|---|---|---|:---:|
| 3 | `(3,2)` | `2/3` | `2/3` | ✓ |
| 4 | `(6,3,2)` | `1/2, 2/3` | `2/3` | ✓ |
| 5 | `(24,6,3,2)` | `1/4, 1/2, 2/3` | `1/2, 2/3` | ✓ |
| 6 | `(120,24,6,3,2)` | `1/5, 1/4, 1/2, 2/3` | **`1/4`**, `1/2, 2/3` | **✗** |
| 7 | `(720,120,24,6,3,2)` | `1/6,…` | **`1/5, 1/4`**, `1/2, 2/3` | **✗** |

The iterated MoveB **apex steps** (`1/4, 1/5, …`) become *internal* per-step `Pr`'s one level up, and fall **below** the BFT-sharp interval `[3/11, 8/11]`. So the naive survivor tower **refutes (CM-rel) at `n ≥ 6`**. The naive tower is therefore *not* the genuine tower — confirming that the "descent" is **essential**, not cosmetic.

## §S2.4 The "descent" is real, essential, HPC-class, and under-specified

The materialised `n = 3` run confirms F21.1's parenthetical "**(the descent of)**" is a *genuine* operation: the recorded `c*_4` **is** reachable from the survivor `D-lift(c*_3)` by a gradient `V`-path **inside the perfect `M_4`** (path length 27). The descent absorbs the bad MoveB apex step into a BFT-sharp first step (recorded `c*_5` has first step `7/15`, not the closure-lift's `1/4` — that is exactly how the descent dodges the §S2.3 catastrophe).

But:
- **The descent target is not canonically pinned.** Among the `212` `2`-cells reachable from the survivor by a gradient `V`-path, `151` are all-BFT-sharp; the minimum `|L|`-profile among those is `(5,3,2)` — *equal to* recorded `c*_4`'s profile — but the min-profile all-BFT-sharp cells span **4 distinct `S_4`-orbits`. Recorded `c*_4` is one of them, not uniquely distinguished by min-profile + BFT-sharpness. (This is precisely F21 §5.2's own "lower-bound argument" — the (CM-struct)(i)+(ii) constraints under-determine `c*_n`.)
- **The descent is HPC-class.** Unlike the cross-boundary cancellation (which is structural — the survivor is a closed-form closure-operator lift), the descent is a gradient-`V`-path move **inside the full `Δ_{n+1}`**. It requires `M_{n+1}` materialised: feasible at `n = 3` (`Δ_4`, `1.5·10⁴` cells), HPC at `n ≥ 4` (`Δ_5` ≈ `3.3·10⁸` cells, `Δ_6` ≈ … ). The cross-boundary cancellation does **not** bypass the HPC; it reduces "find `c*_{n+1}`" to "the descent of `D-lift(c*_n)`", which is still HPC.

## §S2.5 Diagnosis and verdict

> **The cross-boundary Forman cancellation produces `D-lift(c*_n)` — an `M_rel^eq` critical cell — not the recorded `c*_{n+1}`. F21.1's "(the descent of)" is a genuine, essential, separate operation that is (a) canonically under-specified and (b) HPC-class for `n ≥ 4`. The `n = 4` trip-wire as scoped ("the cross-boundary cancellation of `c*_4` must descend to the known `c*_5`") therefore cannot pass: the cancellation alone yields `D-lift(c*_4)`, not `c*_5`.**

This is **RED-tripwire** in the precise sense of the F22-HPC verdict matrix — "*the n=4 cross-boundary cancellation does not descend to the known c*_5: the F21.1 descent picture is [incomplete]*". It is **not** RED-cm-rel-false: (CM-rel) is *not* refuted on the genuine `c*_6, c*_7` — those are simply *not produced*, because the descent rule is not pinned. (The naive survivor tower *would* refute it — §S2.3 — but that tower is not the genuine tower.) It is **not** GREEN-cells-materialised, and **not** AMBER-budget-capped: the bound is structural (the descent gap), not budgetary — the `n = 3` materialised trip-wire ran in `< 1 s`.

**Consequence for the program.** F21.1's *core* (`c*_{n+1}` is the descent of an `M_rel^eq` critical cell) stands; what Session 2 establishes is that "(the descent of)" is **load-bearing in a stronger sense than Session 1 framed it**: it is not merely "the survivor reads off as `c*_{n+1}`", and it is not a cheap by-product of the cross-boundary cancellation. The genuine continuation gate is **the descent rule** — see `docs/state-F22-HPC.md` §5 for the three continuation routes (pin the descent canonically; accept it as HPC on `Δ_{n+1}`; or re-scope the anchor's deliverable to *the precise characterisation of the descent gap*).

## §S2.6 Deliverables (Session 2)

- `scripts/compat_geom_F22_hpc_cell_tracking.py` **Section 10** — the F18 cross-boundary cancellation tracking: `materialised_cross_boundary_n3()` (the `n = 3` trip-wire, exact, reproducible), `naive_closure_lift_tower()` (the `c*_{n+1} := D-lift(c*_n)` tower + the (CM-rel) catastrophe check), `run_cross_boundary_tracking()` (driver). Runtime `< 1 s`.
- This Session-2 section + `docs/state-F22-HPC.md` §5–§6 (cumulative ledger).
- **Trust-surface impact: none.** No new axioms, no Lean changes, no (co)homology HPC datapoint. Pure-Python stdlib, exact arithmetic.

---

## §9. References

### 9.1 Predecessor and sibling mg-tickets

- **mg-a2cb** — F21 (the genuine non-ι-lift canonical chamber-Morse critical cell; re-founding the induction): **GREEN-needs-hpc-anchor.** `docs/compatibility-geometry-F21-genuine-chamber-morse-cell.md` — **Proposition F21.1** (§4, the cofiber-Morse induction — F22-HPC §5 *sharpens* its "(the descent of)" clause), §2 (the exact record `c*_3, c*_4, c*_5` — F22-HPC's seeds), §5 ((CM-struct) ⟹ (CM-rel)), §8 (this ticket, named precisely). **Parent.**
- **mg-4d3a** — F17 (the `n`-uniform `S_n`-equivariant cofiber Morse): **GREEN-equivariant-uniform.** `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md` §1.1 (the `(Q,F)` model), §2 (MoveA/MoveB/PEEL — the lift maps), §4 (the closure operator `c(Q,F)=(Q,[n])` and the `A_n^t` attachment — the terminal reduction), §7.2 (does *not* materialise the two cells — **F22-HPC's target**). **Load-bearing.**
- **mg-d039** — F18 ((UCC.2): `δ_n` injective): **GREEN-ucc2-proven.** The cross-boundary Forman cancellation reducing `crit(M_n) ⊔ crit(M_rel^eq)` to a perfect `M_{n+1}` — the §5.3 / §7 continuation gate.
- **mg-c3fa** — F20 (the `n`-uniform chamber-Morse critical-cell structure): **GREEN-partial.** `docs/compatibility-geometry-F20-chamber-morse-structure.md` §6 (the genuine-`G_6` 12-candidate short list — `c_D@5`'s top `OSA(1,2,2,1)` is among them, §2.3).
- **mg-3839** — F14 (PCR-Lit-2′, the `n=4→5` cofiber cohomology): **GREEN-cofiber-perfect.** `docs/compatibility-geometry-F14-pcr-lit2prime.md`, `scripts/compat_geom_cofiber_morse_n4n5.py` — the MoveA/MoveB/PEEL homology-level reduction this *cell-tracking-upgrades*; the `n = 3` homology cross-check is imported from it.
- **mg-8216** — F10: general-`n` synthesis. **GREEN-conditional.** §6.7 part (iii) — the numerical width-3 conclusion whose structural input this anchor serves.

### 9.2 Mathematical literature

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — discrete Morse theory; the cross-boundary Forman cancellation underlying §5.3.
- P. Hersh, *On optimizing discrete Morse functions*, Adv. Appl. Math. 35 (2005) — the cluster lemma (the fibrewise toggle-apex matchings of MoveA/MoveB).
- J. Jonsson, *Simplicial complexes of graphs*, LNM 1928, Springer 2008 — the patchwork theorem (assembling the fibrewise `S_n`-equivariant matchings into `M_rel^eq`).
- B. Benedetti, F. H. Lutz, *Random discrete Morse theory and a new library of triangulations*, Exp. Math. 23 (2014) — the random-discrete-Morse heuristic used for the `n = 3` materialised cross-check.
- A. Björner, *Topological methods*, in *Handbook of Combinatorics*, Elsevier 1995, §10 — the order-homotopy lemma (the closure/interior-operator collapses); ordinal sums of antichains.
- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984); G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — the `[3/11, 8/11]` BFT-sharp interval.

### 9.3 Code

- `scripts/compat_geom_F22_hpc_cell_tracking.py` — **this F22-HPC / mg-43fb** — the cell-tracking upgrade. Sections: 0 (poset / order-complex utilities), 1 (the `(Q,F)`-model of `A_n`, the F14 reduction objects), 2 (small-complex homology), 3 (Benedetti–Lutz random discrete Morse — the `n = 3` perfect-matching cross-check), 4 (**the cell-tracking lift** — `closure-operator → PEEL → MoveB → MoveA`), 5 (relative-cell verification), 6 ((CM-rel) analysis), 7 (the exact record `c*_3,4,5`), 8 (cross-checks), 9 (driver). Pure-Python stdlib; exact `Fraction`/`int` arithmetic.
- `scripts/compat_geom_cofiber_morse_n4n5.py` (mg-3839), `scripts/compat_geom_F17_equivariant_morse.py` (mg-4d3a) — the homology-level F14-reduction scripts F22-HPC upgrades; the former's `cofiber_homology` is imported for the `n = 3` cross-check.

### 9.4 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (F22-HPC Session 1 is pure internal computation + structural analysis; no external input.)
- 2026-05-14T17:23Z — milestone 1 = the full gap-free width-3 proof, no sketches or gaps. (Session 1 is scrupulously honest: it materialises what it can materialise — `M_rel^eq`'s critical cells, the F17-structural route — confirms (CM-rel) on them, and **precisely identifies** the remaining gate (the F18 cross-boundary cancellation) rather than passing a lift off as the genuine `c*_{n+1}`. The §5 finding is reported as a finding, not hidden.)
- 2026-05-14T20:32Z — PROCEED with the Tier-3 anchor (inform, do not wait). (Done — Session 1; the continuation is scoped in §7 and `docs/state-F22-HPC.md`.)

---

*Polecat: mg-43fb (F22-HPC), Session 1. Branch: `polecat-cat-mg-43fb`. Verdict: **GREEN-partial** — the two critical `(n−1)`-cells of F17's `M_rel^eq` materialised as explicit chains in `PPF_{n+1}` for `n = 3, 4, 5` (the cell-tracking upgrade, F17-structural memory-efficient route); (CM-rel) checked on the anchor data and CONFIRMED at `n = 3, 4, 5` (width-2-OSA tops with size-2 blocks; internal per-step `Pr` all BFT-sharp). Key finding: F17's `M_rel^eq` critical cells carry `c*_n`'s internal structure, not `c*_{n+1}`'s — they are not the chamber-Morse `c*_{n+1}`, which lies in the MoveB filter `Sub`; F21.1's "(the descent of)" is a genuine cell transform via the F18 cross-boundary cancellation — the continuation gate. The genuine `c*_6, c*_7` are not pinned. No new axioms; no Lean changes. Cumulative state: `docs/state-F22-HPC.md`.*
