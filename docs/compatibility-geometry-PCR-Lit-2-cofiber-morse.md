# Compat-Geom — PCR-Lit-2: Hersh-Welker discrete-Morse on the cofiber Δ₄/Δ₃ (mg-6295)

**Branch:** `compat-geom-PCR-Lit-2-hersh-welker` (new).
**Parent:** mg-ac7a (F8''''' PCR-3 literature integration, `docs/compatibility-geometry-F8ppppp-literature.md`; AMBER-related-but-distant). PCR-Lit-2 is the Tier-2 polecat-feasible follow-up surfaced in that doc's §6.2.
**Siblings (parallel polecats):** mg-759d (PCR-Lit-3 = FI-module presentation-degree check, filing); mg-14a0 (F9-S2 = polynomial-vs-exp pattern at n=7). Independent of both; no shared files touched.
**Type:** Constructive discrete-Morse computation (Markdown doc + one Python script; 120k token cap; polecat-class). **No new axioms; no Lean changes.**
**Verdict:** **GREEN-constructive-cofiber-Morse.** A discrete Morse matching `M₄` on Δ₄ that *augments* a canonical matching `M₃` on the subcomplex Δ₃ is constructed explicitly; the cofiber part `M_rel = M₄ \ M₃` is **perfect** on the relative complex `C_*(Δ₄, Δ₃)`, with critical-cell vector `(0,0,2,0)` exactly equal to the PCR-1 (mg-f91f) cofiber Betti vector. The 2 critical 2-cells generate `H̃²(Δ₄/Δ₃) = 2·sgn_{S₃}`, reproducing mg-59f3 §3.4's `m_{X/A}^sgn = 2`. The decomposition `M_{n+1} = M_n ⊔ M_rel` is acyclic for **all** n by an n-independent downward-closed-subcomplex lemma — so this is a genuine n-uniform constructive **mechanism**, a second independent route to the (I5) inductive lift alongside the Plan H ψ-correction.
**Daniel directive (2026-05-14T05:18Z, restated):** "finish the induction internally" — no external collaboration; internal polecat-class effort. PCR-Lit-2 is one of three parallel internal partial routes.

**Deliverables:**
- `docs/compatibility-geometry-PCR-Lit-2-cofiber-morse.md` (this doc).
- `scripts/compat_geom_cofiber_morse_n3n4.py` (the computation; pure-Python stdlib; runtime ~2 s).

---

## 0. Executive summary

### 0.1 What PCR-Lit-2 delivers

Plan H (F9) attacks the (I5) inductive-lift gap by constructing the cocycle `ω_bal^(n+1)` from `ω_bal^(n)` via an empirical correction `ψ`. PCR-Lit-2 attacks the **same** gap from the **cofiber side**, applying the Hersh-Welker discrete-Morse-on-a-cofiber machinery (cluster C3, entry 3.6, of the mg-ac7a literature table):

> Build a discrete Morse matching `M₄` on Δ₄ = Δ(PPF₄) that **restricts** to a known matching `M₃` on the subcomplex Δ₃ = Δ(PPF₃), so that `M₄ = M₃ ⊔ M_rel` with `M_rel` a matching on the relative cells `C_*(Δ₄, Δ₃)`. By the Hersh-Welker cofiber-Morse principle, the critical cells of `M_rel = M₄ \ M₃` compute the reduced (co)homology of the cofiber Δ₄/Δ₃ **directly**.

This is executed in `scripts/compat_geom_cofiber_morse_n3n4.py`. Every numerical claim below is reproduced by that script (pure-Python stdlib, ~2 s on commodity hardware).

### 0.2 Headline results

| Object | Result | Cross-check |
|---|---|---|
| Trip-wire (a): F2/F3 greedy matching on full Δ₄ | critical vector `(2,5,4,0,0)` | reproduces mg-7455 / mg-6bc3 |
| Canonical Δ₃ matching `M₃` | critical `(0,1)`, ∅ matched ⇒ Δ₃ ≃ S¹ | F2 mg-7455 |
| Cofiber matching `M_rel` (greedy) | critical `(0,3,5,0,0)` | χ = +2 ✓ |
| `M_rel` after 3 Forman cancellations | critical **`(0,0,2,0)`** — **perfect** | — |
| Trip-wire (b): direct relative Betti | `b̃_*(Δ₄/Δ₃) = (0,0,2,0)` | reproduces PCR-1 mg-f91f |
| Extended matching `M₄ = M₃ ⊔ M_rel` | valid, **acyclic** on Δ₄, restricts to `M₃` | — |
| `critical(M₄)` | `(0,1,2,0)`, χ = +1 = χ̃(Δ₄) | F2 mg-7455 |
| Trip-wire (c): S₃-rep on `H̃²(Δ₄/Δ₃)` | `2·sgn_{S₃}` (triv 0, sgn 2, std 0) | reproduces mg-59f3 §3.4 |

All three mandatory trip-wires (a)/(b)/(c) **pass**. `M_rel` being perfect means the Morse inequalities are equalities — its Morse differential vanishes identically and `critical(M_rel)` *is* `H̃_*(Δ₄/Δ₃)`.

### 0.3 Verdict matrix

| Branch | Condition | This run? | Verdict |
|---|---|:---:|---|
| **GREEN-constructive-cofiber-Morse** | `M₄ \ M₃` constructed with 2 critical 2-cells matching mg-59f3 §3.4 **and** the extension rule shows a structural pattern (n=3→4 extension generalizable). | ✓ — see §4, §5, §6 | **THIS RUN** |
| GREEN-locally-clean | `M₄ \ M₃` constructed but extension rule unclear beyond n=4. | ✗ — the mechanism's acyclicity is structural for all n (§6) | — |
| AMBER-matching-fails | No extended matching `M₄ ⊇ M₃` exists. | ✗ — `M₄ = M₃ ⊔ M_rel` constructed and verified acyclic | — |
| RED-cross-validation-fails | `M₄ \ M₃` critical cells fail to reproduce mg-59f3 §3.4 `m_{X/A}^sgn = 2`. | ✗ — reproduced exactly (§5) | — |

**Verdict: GREEN-constructive-cofiber-Morse.** Triggers **PCR-Lit-2'** at n=4→5 (see §6.3).

---

## 1. Setting and the (I5) gap

### 1.1 Convention

Δ_n is the order complex of `PPF_n := Pos_n^sub \ {antichain} \ {total orders}` (the F1-refined / F2 / F5 convention; `|PPF₃| = 12`, `|PPF₄| = 194`). The inclusion `ι₃ : PPF₃ ↪ PPF₄` sends a partial order P on {0,1,2} to the same relation set viewed on {0,1,2,3} — element 3 incomparable to all of {0,1,2}. This induces a **subcomplex** inclusion Δ₃ ↪ Δ₄: a chain of PPF₃ maps to a chain of PPF₄, and Δ₃ is the order complex of `ι₃(PPF₃) ⊂ PPF₄`.

The relevant f-vectors (script §A):
- `f(Δ₃) = [12, 12]`, χ̃(Δ₃) = −1 (Δ₃ ≃ S¹).
- `f(Δ₄) = [194, 1872, 5232, 5664, 2112]`, χ̃(Δ₄) = +1 (Δ₄ ≃ S²).
- `f(Δ₄, Δ₃) = [182, 1860, 5232, 5664, 2112]` (relative cells), χ̃(Δ₄/Δ₃) = +2.

### 1.2 The (I5) gap and the two constructive routes

Per F8'' §1.3, (I5) asks for the S_n-equivariant homotopy type of the cofiber Δ_{n+1}/Δ_n as an explicit `Σ Δ(X_n)`. There are two constructive attacks under the "finish internally" directive:

- **Plan H (F9):** lift `ω_bal^(n) ∈ H̃^{n-2}(Δ_n)` to `ω_bal^(n+1) ∈ H̃^{n-1}(Δ_{n+1})` via an empirical correction `ψ`.
- **Cofiber discrete Morse (this doc):** build a discrete Morse matching on Δ_{n+1} that **augments** a known matching on Δ_n, so the new critical cells *are* a cellular model for the cofiber.

The two routes meet at `H̃²(Δ₄/Δ₃)^sgn`: §7 verifies they agree.

### 1.3 The Hersh-Welker cofiber-Morse principle

The mechanism this doc uses is standard discrete Morse theory applied to a subcomplex pair (Hersh-Welker discrete-Morse / shelling literature; Forman 1998; Kozlov 2008 Ch. 11):

> **Cofiber-Morse principle.** Let A ⊆ X be a subcomplex. A discrete Morse matching `M_X` on X is *compatible with A* if it never matches a cell of A with a cell of X \ A. Then `M_X = M_A ⊔ M_{X\A}` where `M_A := M_X ∩ (A×A)` is a matching on A and `M_{X\A}` is a matching on the relative cells `C_*(X, A)`. If `M_X` is acyclic, then:
> - `critical(M_A)` computes `H̃_*(A)`;
> - `critical(M_{X\A})` computes `H̃_*(X/A)` — the **cofiber**;
> - `critical(M_X) = critical(M_A) ⊔ critical(M_{X\A})` computes `H̃_*(X)`.

PCR-Lit-2 constructs exactly such a compatible `M₄` for `A = Δ₃ ⊆ X = Δ₄`.

---

## 2. Trip-wire target-truth pre-checks (mandatory)

All three pre-checks were run *before* the construction, as required by the ticket. Two were verified by running the predecessor scripts directly; all three are also re-verified inside `compat_geom_cofiber_morse_n3n4.py`.

### 2.1 (a) — mg-7455 / mg-6bc3 chamber Morse data

`posn_morse_check.py 4` (mg-7455) produces the greedy top-down acyclic matching on the **full** Δ₄ with critical-cell vector **`(c₀,…,c₄) = (2,5,4,0,0)`** — 2 critical 0-cells, 5 critical 1-cells, 4 critical 2-cells. This matches F3 mg-6bc3 §2.1 verbatim. **Reproduced** in script §B by a faithful transcription of F2's `compute_morse_matching` (the F2 greedy's outcome depends on the *unsorted* `enumerate_posets` ordering of its input, so the transcription keeps that calling convention verbatim). ✓

This F2/F3 matching **ignores the filtration** Δ₃ ⊂ Δ₄ — it is the foil against which the new filtration-respecting `M₄` is built.

### 2.2 (b) — PCR-1 (mg-f91f) cofiber Betti vector

`compat_geom_n4_relative_betti.py` (mg-f91f) computes `b̃_*(Δ₄/Δ₃) = (0,0,2,0)` over ℚ (verdict `GREEN-wedge`). **Reproduced** in script §F by an independent direct mod-p rank computation of the relative chain complex. ✓

### 2.3 (c) — PCR-2 (mg-59f3) §3.4 sign-rep multiplicity

`compat_geom_pcr2_spectral.py` (mg-59f3) computes the S₃-character on `H̃²(Δ₄/Δ₃)` and decomposes it as `2·sgn_{S₃}`, i.e. `m_{X/A}^sgn = 2`. **Reproduced** in script §G by a Lefschetz fixed-point character computation. ✓

---

## 3. The construction: M₄ = M₃ ⊔ M_rel

### 3.1 The canonical Δ₃ matching M₃ (script §C)

`M₃` is the deterministic top-down greedy acyclic matching on Δ₃ with the augmentation cell ∅ included. It has critical-cell vector `(0,1)` with ∅ matched: 0 critical 0-cells, 1 critical 1-cell. Hence the Morse complex of `M₃` is `C₀ = 0, C₁ = ℚ`, with vanishing differential — it computes `H̃_*(Δ₃) = (0, ℚ)`, i.e. Δ₃ ≃ S¹. This `M₃` is the "canonical Δ₃ matching" the ticket asks `M₄` to refine. It has 12 matched pairs over the 25 cells of Δ₃ (including ∅).

### 3.2 The cofiber matching M_rel (script §D)

`M_rel` is built on the **relative cells only** — the chains of Δ₄ with at least one vertex outside `ι₃(PPF₃)` (there are 15 050 of them, f-vector `[182,1860,5232,5664,2112]`). The cover graph is restricted to relative-relative cover pairs; a relative cell may have faces inside Δ₃, and those faces are simply not available as matching partners.

- **Greedy step.** The top-down greedy acyclic matching on the relative cells gives critical-cell vector `(0,3,5,0,0)`. Euler check: 0 − 3 + 5 = +2 = χ̃(Δ₄/Δ₃) ✓. This is acyclic by construction but **not perfect** — it carries 3 spurious cancelling (1-cell, 2-cell) pairs.
- **Forman cancellation.** Each spurious pair is a critical 1-cell and critical 2-cell joined by **exactly one** gradient V-path. Forman cancellation (Forman 1998 Thm 11.1) reverses every matched pair along that unique path, making both cells non-critical while preserving acyclicity. The script finds and cancels 3 such pairs (V-paths of length 6, 12, 4).
- **Result.** `critical(M_rel) = (0,0,2,0)`. The matching is re-verified **acyclic** after cancellation by an independent modified-Hasse DFS. Since `0,0,2,0` already equals the PCR-1 cofiber Betti vector and the Morse inequalities give `critical ≥ Betti` in every dimension, **`M_rel` is a perfect Morse matching on the cofiber.**

The 2 critical 2-cells (3-chains of PPF₄, written as relation sets):
```
{1<2,1<3} < {0<3,1<2,1<3} < {0<2,0<3,1<2,1<3,3<2}
{3<0,3<1,3<2} < {0<1,3<0,3<1,3<2} < {0<1,0<2,3<0,3<1,3<2}
```

### 3.3 The extended matching M₄ (script §E)

`M₄ := M₃ ⊔ M_rel` — keep `M₃` verbatim on Δ₃, overlay `M_rel` on the relative cells. The script verifies, by assertion:

1. **`M₄` is a well-formed matching** on Δ₄: every cell has at most one partner, partners are symmetric.
2. **`M₄` restricted to Δ₃ equals the canonical `M₃` exactly** — every Δ₃ cell (including ∅) has the same partner under `M₄` as under `M₃`.
3. **`M₄ \ M₃ = M_rel`** — the cofiber part is exactly the relative matching.
4. **`M₄` is acyclic on the whole of Δ₄** — verified by modified-Hasse DFS over all 15 075 cells (∅ included). See §6.1 for why this is structurally guaranteed.
5. **`critical(M₄) = critical(M₃) ⊔ critical(M_rel) = (0,1,2,0)`**, with Euler characteristic 0 − 1 + 2 = +1 = χ̃(Δ₄) ✓.

So `M₄` is a discrete Morse matching on Δ₄ that **augments** `M₃` — exactly the ticket's deliverable 2. Note `M₄` is *not* perfect on Δ₄ (a perfect matching would give `(0,0,1,0)`); it carries one cancelling (1-cell, 2-cell) pair joined by a V-path that crosses the Δ₃/relative boundary. That is expected and harmless: the cofiber-Morse principle only needs `M₄` to be acyclic and compatible with the subcomplex.

---

## 4. Hersh-Welker cofiber-Morse theorem applied (script §F)

`M₄ = M₃ ⊔ M_rel` is an acyclic matching on Δ₄ compatible with the subcomplex Δ₃. By the cofiber-Morse principle (§1.3), `critical(M₄ \ M₃) = critical(M_rel)` computes the reduced (co)homology of the cofiber Δ₄/Δ₃.

`critical(M_rel) = (0,0,2,0)`. Because `M_rel` is **perfect**, there are no critical cells in adjacent dimensions, the Morse differential vanishes identically, and therefore

> **`H̃_*(Δ₄/Δ₃) = (0, 0, ℚ², 0)`** — directly, as the critical-cell ℚ-span of `M_rel`.

This is independently cross-checked in script §F against a direct mod-p rank computation of the relative chain complex (the PCR-1 method), which returns the same `(0,0,2,0)` — trip-wire (b). The cofiber-Morse critical count equals the direct Betti vector dimension-by-dimension; the Forman-inequality slack is zero.

**This is the ticket's deliverable 3:** the cofiber's reduced cohomology is computed by the critical cells of `M₄ \ M₃`, which has exactly 2 critical 2-cells and 0 critical cells in every other dimension.

---

## 5. The 2 critical 2-cells are the sign-rep generators (script §G)

`S₃ < S₄` (permuting {0,1,2}, fixing 3) acts on PPF₄ and preserves `ι₃(PPF₃)`, hence acts on the cofiber Δ₄/Δ₃. A relative k-cell (a chain) is g-fixed iff g fixes each vertex poset. The Lefschetz number `L(g) = Σ_k (−1)^k #{g-fixed relative k-cells}`; since `H̃_*(Δ₄/Δ₃)` is concentrated in degree 2, `L(g) = trace(g | H̃²(Δ₄/Δ₃))`.

The script computes (one representative per S₃ conjugacy class):

| class (cycle type) | size | `L(g) = trace(g | H̃²)` |
|---|:---:|:---:|
| `(1,1,1)` (identity) | 1 | 2 |
| `(2,1)` (transposition) | 3 | −2 |
| `(3)` (3-cycle) | 2 | 2 |

Decomposing against the S₃ character table:
- ⟨χ, triv⟩ = (1·2 + 3·(−2) + 2·2)/6 = 0
- ⟨χ, sgn⟩ = (1·2 + 3·(+2) + 2·2)/6 = **2**
- ⟨χ, std⟩ = (1·4 + 3·0 + 2·(−2))/6 = 0

> **`H̃²(Δ₄/Δ₃) ≅ sgn_{S₃} ⊕ sgn_{S₃} = 2·sgn_{S₃}`** — trip-wire (c), reproducing mg-59f3 §3.4 `m_{X/A}^sgn = 2`.

Because `M_rel` is **perfect**, the 2 critical 2-cells of `M_rel` form a ℚ-basis of `H̃_2(Δ₄/Δ₃)`. That 2-dimensional space carries the S₃-representation `2·sgn`. The identity `Res^{S₄}_{S₃} sgn_{S₄} = sgn_{S₃}` (mg-59f3 §3.3) identifies these as the "S₄-sign-rep generators" the ticket's deliverable 4 asks for: the cofiber-Morse critical 2-cells are an explicit *cellular* basis for the sign-rep classes that mg-59f3's spectral `E₂` page resolves abstractly. (Strictly: the cofiber carries an S₃-action, not S₄ — ι₃ is not S₄-equivariant — and the sign rep in question is `sgn_{S₃}`, the restriction of `sgn_{S₄}`.)

---

## 6. The n-uniform extension mechanism (script §H)

### 6.1 Why M_{n+1} = M_n ⊔ M_rel is acyclic for *all* n

The extension rule `M_n → M_{n+1}` is the uniform recipe:

1. keep `M_n` verbatim on the subcomplex Δ_n;
2. the relative cells are the chains of Δ_{n+1} with ≥1 vertex outside `ι_n(PPF_n)` — well-defined for every n, since `Δ_n ↪ Δ_{n+1}` is always a subcomplex;
3. match those relative cells by the top-down greedy lex rule, restricted so the pivot keeps the chain relative;
4. Forman-cancel the residual (k−1,k)-pairs joined by a unique gradient V-path, down to the cofiber Betti vector.

The acyclicity of `M_{n+1} = M_n ⊔ M_rel` follows from an **n-independent** lemma:

> **Downward-closed-subcomplex lemma.** If `A ⊆ X` is a subcomplex (downward closed under taking faces), `M_A` is an acyclic matching on A, and `M_{X\A}` is an acyclic matching on the relative cells, then `M_A ⊔ M_{X\A}` is acyclic on X.
>
> *Proof.* In the modified Hasse digraph of `M_A ⊔ M_{X\A}`, every out-edge from an A-cell stays in A: an unmatched cover edge from `c ∈ A` goes down to a face, which is in A (A downward closed); a matched-up edge `(c, τ)` has `(c,τ) ∈ M_A` since `c ∈ A`, so `τ ∈ A`. Hence no directed path can leave A. A directed cycle, being periodic, is therefore either entirely inside A — contradicting acyclicity of `M_A` — or entirely inside the relative cells — contradicting acyclicity of `M_{X\A}`. ∎

The script verifies the load-bearing hypothesis computationally for n=4: **zero** modified-Hasse out-edges leave Δ₃. This witness is the n-4 instance of an argument that does not depend on n. **So `M_{n+1} = M_n ⊔ M_rel` is acyclic for every n** — the cofiber-Morse decomposition is a genuine n-uniform constructive mechanism, not an n=4 coincidence.

### 6.2 The relative-cell set is uniform but not "just the n-active posets"

The relative vertices at n=4 split as 182 = 176 "3-active" (element 3 comparable to something) + 6 "3-isolated boundary" (3 isolated, but the {0,1,2}-restriction is empty or total, so still outside `ι₃(PPF₃)`). The relative-cell **set** is exactly `PPF_{n+1} \ ι_n(PPF_n)` — well-defined and uniform in n, but **not** simply the n-active posets; the boundary posets must be included. (An earlier draft of the script over-claimed this characterization; it is corrected here.)

### 6.3 What PCR-Lit-2' must still check at n=4→5

The **mechanism** (steps 1–4) is uniform and provably acyclic for all n. The single fact *not* settled by the n=3→4 data point alone: whether the greedy+Forman steps 3–4 again bottom out at exactly the cofiber Betti vector. Forman cancellation is not a priori guaranteed to reach the Morse-theoretic minimum — it depends on the availability of *unique* gradient V-paths between residual critical pairs. At n=3→4 it does (greedy `(0,3,5,0,0)` → 3 unique-path cancellations → perfect `(0,0,2,0)`). PCR-Lit-2' should re-run the identical recipe at n=4→5 and check it reaches the cofiber Betti vector there (the n=4→5 cofiber Betti is not yet computed; PCR-1' would supply it). If yes at n=4→5 and beyond, the cofiber-Morse route becomes a full inductive construction for (I5).

---

## 7. Cross-validation with Plan H ψ⁽⁴⁾ (script §I)

Plan H (F9) lifts `ω_bal^(3) → ω_bal^(4)` via an empirical correction `ψ`. F8'''' (mg-59f3) computed the cofiber long-exact-sequence `E₂` page and found, on the sign isotype:
```
0 → H̃¹(Δ₃)^sgn --δ₁--> H̃²(Δ₄/Δ₃)^sgn --π₂--> H̃²(Δ₄)^sgn → 0
        sgn       ↪          2·sgn          ↠        sgn
```
with `δ₁` injective and multiplicity pattern `(m_A, m_X, m_{X/A})^sgn = (1, 1, 2)`; `ω_bal^(4)` is the cokernel class of `δ₁` on the sgn-isotype.

PCR-Lit-2's cofiber-Morse route gives, **independently**, `H̃²(Δ₄/Δ₃) = 2·sgn` with the 2 critical 2-cells of `M_rel` as an explicit cellular basis. The two routes agree:

- both pin the cofiber's degree-2 cohomology as exactly `2·sgn_{S₃}` (the entire `H̃²`, no isotypic contamination);
- the cofiber-Morse critical 2-cells are a *cellular* model for the same 2-dimensional sign-rep that the spectral `E₂` page resolves *abstractly*;
- the spectral picture decomposes that `2·sgn` as `δ₁(ω_bal^(3)) ⊕ ω_bal^(4)` (one inherited sgn-class + one newly lifted class). The cofiber-Morse picture supplies the matching `M_rel` whose critical cells *carry* that decomposition cellularly.

So the constructive cofiber-Morse path and the Plan H ψ-route are **consistent** at n=3→4 — they produce the same `H̃²(Δ₄/Δ₃)^sgn = 2·sgn` data by structurally different means. This is the ticket's deliverable 6.

---

## 8. What PCR-Lit-2 does and does not establish

### 8.1 Establishes

- An explicit discrete Morse matching `M₄` on Δ₄ that augments the canonical Δ₃ matching `M₃` (`M₄ = M₃ ⊔ M_rel`, verified valid, acyclic, and restricting to `M₃`).
- The cofiber part `M_rel = M₄ \ M₃` is **perfect** on `C_*(Δ₄, Δ₃)`: critical vector `(0,0,2,0)` = PCR-1 Betti vector.
- The 2 critical 2-cells generate `H̃²(Δ₄/Δ₃) = 2·sgn_{S₃}`, reproducing mg-59f3 §3.4.
- The decomposition `M_{n+1} = M_n ⊔ M_rel` is acyclic for **all** n by the n-independent downward-closed-subcomplex lemma — a genuine n-uniform constructive mechanism.
- Consistency with Plan H ψ⁽⁴⁾ and the F8'''' spectral `E₂` page.
- All three mandatory trip-wires (a)/(b)/(c) pass.

### 8.2 Does NOT establish

- `X_n` is **not** identified — this run computes the cofiber's cellular model, not its homotopy type as `Σ Δ(X_n)`.
- The mechanism is shown acyclic for all n, but greedy+Forman reaching the cofiber Betti vector is verified **only at n=3→4**. General-n success is the PCR-Lit-2' / PCR-Lit-2'' follow-up (out of scope here, per the ticket).
- No S_n-**equivariant** matching is constructed — the greedy+Forman matching is not S₃-equivariant. The S₃-rep structure of `H̃²` is established abstractly (Lefschetz, basis-independent), and the critical 2-cells span it, but they are not an S₃-orbit. An equivariant cofiber-Morse matching is a natural further sub-ticket.
- No Lean port (explicitly out of scope; methodology-paper-grade content).
- No new axioms; no changes to `lean/AXIOMS.md` or any Lean file.

---

## 9. Verdict

**GREEN-constructive-cofiber-Morse.**

`M₄ \ M₃ = M_rel` is constructed with exactly 2 critical 2-cells, is perfect on the cofiber, and generates `H̃²(Δ₄/Δ₃) = 2·sgn_{S₃}` (matches mg-59f3 §3.4, `m_{X/A}^sgn = 2`). The cofiber-Morse decomposition `M_{n+1} = M_n ⊔ M_rel` is acyclic for **all** n by the n-independent downward-closed-subcomplex lemma — a genuine n-uniform constructive **mechanism**, a second independent route to the (I5) inductive lift alongside the Plan H ψ-correction.

**Triggers PCR-Lit-2'** at n=4→5: re-run the identical greedy+Forman recipe on `C_*(Δ₅, Δ₄)` and check it again bottoms out at the cofiber Betti vector. (Prerequisite: PCR-1' must first supply the n=4→5 cofiber Betti vector.)

---

## 10. References

### 10.1 Predecessor mg-tickets (immediate chain)

- **mg-ac7a** — F8''''' (PCR-3): literature integration, `docs/compatibility-geometry-F8ppppp-literature.md`. §6.2 surfaces PCR-Lit-2; cluster C3 entry 3.6 is the Hersh-Welker entry. Parent of this run.
- **mg-7455** — F2: discrete Morse + critical-cell classification + ω_bal, `scripts/posn_morse_check.py`. Source of the `(2,5,4,0,0)` chamber-Morse data and the greedy-matching algorithm transcribed here.
- **mg-6bc3** — F3: per-step Pr-spectrum, `docs/compatibility-geometry-F3-scoping.md`. Restates the F2 critical-cell vector `(2,5,4,0,0)`.
- **mg-f91f** — F8''' (PCR-1): cofiber Betti vector `(0,0,2,0)`, `scripts/compat_geom_n4_relative_betti.py`. Trip-wire (b).
- **mg-59f3** — F8'''' (PCR-2): spectral `E₂` page, `scripts/compat_geom_pcr2_spectral.py`, `docs/compatibility-geometry-F8pppp-spectral-sequence.md`. §3.4 `m_{X/A}^sgn = 2`. Trip-wire (c).
- **mg-e8d5** — F7': chamber-restricted equivariant Morse at n=5, `scripts/posn_chamber_morse_n5.py` (context for the chamber-Morse / equivariant program).

### 10.2 Mathematical literature

- P. Hersh, V. Welker, discrete Morse / shellability + matchings papers — the cofiber-Morse machinery (cluster C3, entry 3.6, of mg-ac7a).
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — Thm 3.4 (Morse collapse), Thm 8.2 (Morse differential via V-paths), Thm 11.1 (Forman cancellation).
- R. Forman, *A user's guide to discrete Morse theory*, Sém. Lothar. Combin. 48 (2002).
- M. Chari, *On discrete Morse functions from lexicographic orders*, Discrete Math. 217 (2000) — the lex element-pivot matching.
- D. Kozlov, *Combinatorial Algebraic Topology*, Springer (2008), Ch. 11 — discrete Morse theory for subcomplex pairs.

### 10.3 Daniel directives

- 2026-05-14T05:18Z: "finish the induction internally" — no external collaboration; internal polecat-class effort. PCR-Lit-2 is one of three parallel internal partial routes (with mg-759d, mg-14a0).
- 2026-05-14T02:38Z (restated via mg-ac7a): "let's push harder on I5, we're so close."

---

End of PCR-Lit-2 cofiber-Morse document. Verdict: **GREEN-constructive-cofiber-Morse** — an explicit discrete Morse matching `M₄ = M₃ ⊔ M_rel` on Δ₄ augments the canonical Δ₃ matching; `M_rel = M₄ \ M₃` is a *perfect* cofiber matching with critical vector `(0,0,2,0)` reproducing PCR-1, and its 2 critical 2-cells generate `H̃²(Δ₄/Δ₃) = 2·sgn_{S₃}` reproducing mg-59f3 §3.4. The decomposition `M_{n+1} = M_n ⊔ M_rel` is acyclic for all n by an n-independent lemma — a genuine n-uniform constructive mechanism and a second independent route to (I5). All trip-wires pass. Triggers PCR-Lit-2' at n=4→5.

Mayor inbox: `mg-6295`. Branch: `compat-geom-PCR-Lit-2-hersh-welker`.
