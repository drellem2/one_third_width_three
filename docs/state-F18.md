# state-F18 — cumulative state ledger for F18 ((UCC.2): `δ_n` injective for all `n`) (mg-d039)

**Ticket:** mg-d039 — F18, THE critical-path ticket. Structural argument (order-complex topology / the order-homotopy lemma); 400k cap; multi-session-able.
**Branch:** `polecat-cat-mg-d039`.
**Parent:** mg-4d3a (F17, GREEN-equivariant-uniform) §7.3 (the (UCC.2) handle, `ι_n^* = 0` form) + §8.3 (the recommended F18 target — attack `ι_n` directly).
**Chain:** mg-b352 (F11) → mg-ecf6 (F13) → mg-3839 (F14) → mg-8355 (F15) → mg-f893 (F16) → mg-4d3a (F17) → **mg-d039 (F18)**.
**Deliverables:** (D1) `docs/compatibility-geometry-F18-ucc2-delta-injective.md`; (D2) `docs/state-F18.md` (this file); (D3) `scripts/compat_geom_F18_ucc2_delta_injective.py`.
**Constraints:** no new axioms; no Lean changes; 400k cap; cumulative state doc; internal only (route (iii)/mg-b345 stays PARKED — its escalation trigger is definitively unmet, the internal route delivered both (UCC.1) and (UCC.2)).

This file survives session boundaries; a future session re-checks the invariants in §3 before extending.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-d039) — DONE

**Goal:** Prove **(UCC.2)** — `δ_n : H̃^{n-2}(Δ_n) → H̃^{n-1}(Δ_{n+1}/Δ_n)` injective, n-uniformly, equivalently `ι_n^* = 0` on `H̃^{n-2}` — using Hyp(3..n) + F17 but NOT Hyp(n+1) (circularity guard). The attack lives on the absolute tower `(Δ_n)_n` and the inclusion `ι_n` (F17 §8.3).

| Item | Status | Output |
|---|---|---|
| Read parents: F17 (mg-4d3a) + doc + state; F10 (mg-8216) §6 + §7; F15 (mg-8355) §4 + §6; F16 (mg-f893) §5 + state; mg-59f3 ((UCC.2)@n=3) | ✅ | — |
| **Lemma 2.2: `ω_n ∈ PPF_{n+1}`** | ✅ **proven** | D1 §2.1 — `ω_n = {(n,b):b∈[n]}` ("new element `n` below all of `[n]`") is a proper partial order on `[n+1]`. Combinatorics only. |
| **Lemma 2.3: `κ_n` well-defined `PPF_n → PPF_{n+1}`** | ✅ **proven — the one load-bearing combinatorial lemma** | D1 §2.1 — `κ_n(x) = x ∪ ω_n ∈ PPF_{n+1}` for every `x ∈ PPF_n`. Transitivity (the only new compositions `(n,b)·(b,c)` land back in `ω_n`); **non-totality** (a total `x ∪ ω_n` forces `x` total on `[n]`, contradiction). Combinatorics only — no hypothesis. |
| **Lemma 2.4: `κ_n` order-preserving + `S_n`-equivariant** | ✅ **proven** | D1 §2.1 — `x⊆x' ⟹ x∪ω_n ⊆ x'∪ω_n`; `ω_n` is `S_n`-fixed (`S_n` permutes `[n]`, fixes `n`), so `g·κ_n(x) = κ_n(g·x)`. |
| **Prop. 2.5: the zig-zag `ι_n ≤ κ_n ≥ const_{ω_n}`** | ✅ **proven** | D1 §2.2 — three order-preserving `S_n`-equivariant maps `PPF_n → PPF_{n+1}`; `ι_n(x) = x ⊆ x∪ω_n = κ_n(x) ⊇ ω_n`, both inclusions strict. |
| **Lemma 3.1: order-homotopy lemma** | ✅ **standard, recalled with the prism proof** | D1 §3.1 — order-preserving `f ≤ g : P → Q` ⟹ `|Δ(f)| ≃ |Δ(g)|`, equivariantly if `f,g` are. Björner *Topological methods* §10 / Kozlov Ch. 10 / Quillen §1.3. Prism proof included for self-containedness. |
| **Theorem 3.2: `ι_n` null-homotopic** | ✅ **proven — UNCONDITIONAL, `S_n`-equivariant** | D1 §3.2 — `|ι_n| ≃_{S_n} |κ_n| ≃_{S_n} const_{ω_n}` via the zig-zag (Prop. 2.5) + Lemma 3.1. **No `Hyp(m)`, no `(UCC)`, no F17 — unconditional.** Explicit chain null-homotopy `D = P' − P` with `∂D + D∂ = (ι_n)_# − const_#` (eq. 3.3). |
| **Theorem 4.1: (UCC.2) for all `n`** | ✅ **proven — UNCONDITIONAL** | D1 §4.1 — `ι_n` null-homotopic ⟹ `ι_n^* = 0`, `ι_{n,*} = 0` in all degrees ⟹ (cofiber LES exactness) `ker(δ_k) = im(ι_n^*) = 0` ⟹ `δ_k` injective all `k`, in particular `δ_n`. **(UCC.2)** for all `n ≥ 3`. |
| **Circularity guard discharged** | ✅ **vacuously — proof uses NO hypothesis** | D1 §4.2 — step-by-step table: every step (Lemmas 2.2–2.4, Prop. 2.5, Lemma 3.1, Thms 3.2, 4.1) uses only combinatorics + standard topology. `Hyp(n+1)` never enters; nothing is assumed. Contrast: mg-59f3's `n=3` route used `H̃^1(Δ_4)=0 = Hyp(n+1)` — circular for general `n`; F18 replaces it. |
| **Corollary 5.1: cofiber LES splits** | ✅ **proven** | D1 §5.1 — `ι_n^* = 0` ⟹ `H̃^k(Δ_{n+1}/Δ_n) ≅ H̃^{k-1}(Δ_n) ⊕ H̃^k(Δ_{n+1})` as `S_n`-reps. With F17's `2·H̃^{k-1}(Δ_n)` ⟹ `H̃^k(Δ_{n+1}) ≅ H̃^{k-1}(Δ_n)` — the degree-shift engine. |
| **Corollary 5.2: (UCC) COMPLETE** | ✅ | D1 §5.2 — (UCC.1) ⟺ Hyp(n) (F17), (UCC.2) unconditional (F18). |
| **Theorem 5.3: F10 cohomological core UNCONDITIONAL** | ✅ **proven** | D1 §5.3 — induction `Hyp(n) →[F17] (UCC.1)@n ∧ (UCC.2)@n →[F18+F10§6.2] Hyp(n+1)`, base `Hyp(3)`. `Hyp(n)` all `n`; H-Cox + sgn at general `n`; `ω_bal^{(n)}` exists/unique with `±1` pairing. |
| **Verification harness** `compat_geom_F18_ucc2_delta_injective.py` | ✅ **runs, 43 677/43 677 checks pass (~2s)** | D3 — `κ_n` well-defined + `S_n`-equivariant (`n=3,4,5`); zig-zag `(∗)`; prism poset maps `H, H'` order-preserving; **chain null-homotopy `∂D+D∂ = ι_#−const_#` on every simplex of `Δ_n`** (`n=3,4`, exact integers); homology anchor `Betti(Δ_3)=(0,1)`, `Betti(Δ_4)=(0,0,1,0,0)` `= Hyp(3),Hyp(4)`. |
| **Verdict** | ✅ **GREEN-ucc2-proven** | D1 §7 — (UCC.2) proven for all `n`, unconditionally, non-circularly. (UCC) COMPLETE; F10 cohomological core UNCONDITIONAL. |
| Route (iii) trigger | ✅ **definitively unmet** | D1 §6.2, §7.2 — the internal route delivered both halves of (UCC); route (iii)/mg-b345 stays PARKED. |
| Trust-surface impact | ✅ none | D1 §7.3 — no new axioms, no Lean changes, no HPC. Harness pure-Python stdlib ~2s. |

**Verdict: GREEN-ucc2-proven.** The inclusion `ι_n : Δ_n ↪ Δ_{n+1}` is null-homotopic for every `n ≥ 3`, by the explicit `S_n`-equivariant poset zig-zag `ι_n ≤ κ_n ≥ const_{ω_n}` with `κ_n(x) = x ∪ ω_n` ("cone the new element `n` below everything"). The construction uses no hypothesis whatsoever — unconditional, hence non-circular by construction. Therefore `ι_n^* = 0`, `δ_n` is injective, **(UCC.2) holds for all `n`**. With F17 ((UCC.1) ⟺ Hyp(n)), **(UCC) is COMPLETE** and the **F10 cohomological core is UNCONDITIONAL** (Theorem 5.3). The crown-jewel ticket closes.

**Nothing left undone within F18's scope.** All three deliverables emitted in Session 1. The 400k cap was not approached. F18 did not need to be multi-session; the ledger format is kept per `feedback_polecat_cumulative_state_doc` in case the mayor reopens it.

**If F18 is reopened for a Session 2** — the natural in-scope continuations: (a) extend the chain-level harness certification to `n = 5` (currently `n = 3,4`; `n = 5` is structural-only because `Δ_5` is large — this is polish, the structural checks already prove Theorem 3.2 at `n = 5`); (b) make the LES-splitting of Corollary 5.1 fully explicit at the cochain level with the `q_n`-section. Neither is load-bearing. **The genuine next step is a new ticket** — targeting **(ICOP-step)** (F10 §5.4) and/or the **width-3 reduction bridge** (F10 §7.3), the two remaining conditional inputs of the *numerical* width-3 conclusion (F10 §7.4) — a PM call. These are now the program's load-bearing open items; both are verified `n ≤ 6` and reduced to clean uniform sub-statements; neither is part of (UCC) and neither was touched by F18.

---

## §2. The result, in one screen (reproduce-on-resume)

- **Object.** `Δ_n = Δ(PPF_n)`; `ι_n : Δ_n ↪ Δ_{n+1}` the standard order-ideal inclusion (new element `n` isolated). Cofiber LES of the (good) pair `(Δ_{n+1}, Δ_n)`: `… → H̃^k(Δ_{n+1}/Δ_n) → H̃^k(Δ_{n+1}) →^{ι_n^*} H̃^k(Δ_n) →^{δ_n} H̃^{k+1}(Δ_{n+1}/Δ_n) → …`, exact, unconditional. **(UCC.2)(n):** `δ_n` injective ⟺ (exactness) `ι_n^* = 0` on `H̃^{n-2}`.
- **The cone element.** `ω_n := {(n,b) : b ∈ [n]}` — the new element `n` below all of `[n]`, `[n]` an internal antichain. `ω_n ∈ PPF_{n+1}` (Lemma 2.2), `S_n`-fixed.
- **The cone map (Lemma 2.3, the one load-bearing combinatorial lemma).** `κ_n : PPF_n → PPF_{n+1}`, `κ_n(x) = x ∪ ω_n`. Well-defined: `x ∪ ω_n` is transitively closed (the only new compositions land in `ω_n`) and **non-total** (a total `x ∪ ω_n` would force `x` total on `[n]` — impossible for `x ∈ PPF_n`). Order-preserving + `S_n`-equivariant (Lemma 2.4).
- **The zig-zag (Prop. 2.5).** `ι_n(x) = x ⊆ x ∪ ω_n = κ_n(x) ⊇ ω_n = const_{ω_n}(x)` — pointwise, `S_n`-equivariantly. Three comparable order-preserving maps `PPF_n → PPF_{n+1}`.
- **Theorem 3.2 (the null-homotopy theorem, UNCONDITIONAL).** Order-homotopy lemma (Lemma 3.1: `f ≤ g` ⟹ `|Δ(f)| ≃ |Δ(g)|`) applied twice: `|ι_n| ≃_{S_n} |κ_n| ≃_{S_n} const_{ω_n}`. So `ι_n` is `S_n`-equivariantly null-homotopic, for every `n ≥ 3`, with **no hypothesis used**. Explicit chain null-homotopy `D = P' − P`, `∂D + D∂ = (ι_n)_# − const_#`.
- **Theorem 4.1 ((UCC.2), UNCONDITIONAL).** `ι_n` null-homotopic ⟹ `ι_n^* = 0` in all degrees ⟹ `ker(δ_k) = im(ι_n^*) = 0` ⟹ `δ_k` injective all `k`. **(UCC.2) for all `n ≥ 3`.**
- **Circularity guard (§4.2).** Discharged *vacuously*: the proof uses no `Hyp(m)`, no `(UCC)`, no F17 — it is unconditional. `Hyp(n+1)` is never invoked. (Contrast mg-59f3's `n=3` route, which used `H̃^1(Δ_4)=0 = Hyp(n+1)` — circular for general `n`.)
- **Corollaries 5.1–5.3.** LES splits: `H̃^k(Δ_{n+1}/Δ_n) ≅ H̃^{k-1}(Δ_n) ⊕ H̃^k(Δ_{n+1})`; with F17 ⟹ `H̃^k(Δ_{n+1}) ≅ H̃^{k-1}(Δ_n)` (degree-shift engine). **(UCC) COMPLETE.** **F10 cohomological core UNCONDITIONAL** (`Hyp(n)` all `n`).
- **What remains for the FULL width-3 theorem.** The *cohomological core* (F10 parts (i)–(ii)) is unconditional. The *numerical width-3 conclusion* (F10 part (iii)) additionally rests on **(ICOP-step)** (F10 §5.4) + the **width-3 reduction bridge** (F10 §7.3) — F10 §7.4's two secondary inputs, verified `n ≤ 6`, reduced to clean sub-statements, NOT part of (UCC), NOT touched by F18.
- **Verdict.** GREEN-ucc2-proven. (UCC.2) proven, (UCC) complete, F10 cohomological core unconditional. Route (ii) stays closed (F16); route (iii) stays parked (escalation definitively unmet).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **`PPF_n` convention** — nonempty, non-total partial orders on `[n]` (= transitively-closed irreflexive antisymmetric relation sets), ordered by relation-set inclusion; `(a,b)` means `a ≺ b`. `|PPF_n| = 12, 194, 4110` at `n = 3,4,5`. `ι_n` = "new element `n` isolated"; an order-ideal inclusion, so `(Δ_{n+1},Δ_n)` is a good pair. (F1-refined / F14 §0.2 / F17 §1.)
- **The cofiber LES is exact for every `n,k` with no hypothesis** — standard LES of a pair; `H̃^k(Δ_{n+1},Δ_n) = H̃^k(Δ_{n+1}/Δ_n)` because `ι_n` is a subcomplex inclusion (cofibration). The reformulation `(UCC.2)(n) ⟺ ι_n^* = 0 on H̃^{n-2}` is F17 §7.3 — pure exactness.
- **Lemma 2.3 (`κ_n` well-defined) is the one load-bearing combinatorial lemma** — and it is *unconditional*. The non-totality argument is the crux: `κ_n(x) = x ∪ ω_n` total on `[n+1]` ⟹ `x` total on `[n]` (every relation between two elements of `[n]` is already in `x`) ⟹ `x ∉ PPF_n`. Re-verify this argument before extending.
- **Order-homotopy lemma** (Björner *Topological methods* §10) — order-preserving `f, g : P → Q` with `f ≤ g` pointwise ⟹ `|Δ(f)| ≃ |Δ(g)|`, equivariantly when `f,g` are. F17 cited the `f ≥ id` / `f ≤ id` (closure/interior operator) special case; F18 uses the general "two comparable maps" case — same section, and the prism proof is recalled in D1 §3.1.
- **Theorems 3.2, 4.1 are UNCONDITIONAL** — they use no `Hyp`, no `(UCC)`, no F17, no per-`n` computation. This is *stronger* than the ticket asked ("prove (UCC.2)(n) without assuming Hyp(n+1)"): F18 proves it without assuming *anything*. The circularity guard is discharged vacuously (D1 §4.2 step table).
- **Cohomology vs homology** — F18 null-homotopes `ι_n`, so `ι_n^* = 0` and `ι_{n,*} = 0` *both* hold, in *all* degrees; over `ℚ` these are dual and the distinction is immaterial. The cofiber-LES conclusion `δ_n` injective is stated in cohomology (F10 / (UCC.2) convention).
- **(UCC.2) is independent of the F17 mechanism** — confirmed from both sides: F17 §7.3 said F17 neither needs nor produces (UCC.2); F18 confirms (UCC.2) is *unconditional*, downstream of nothing. F16 §5's parallel finding (route (ii) independent of (UCC.2)) is consistent.
- **Consistency with established datapoints** — `δ_n` injective is consistent with: mg-59f3 (`δ_3` injective at `n=3`); F15 §6 (`(UCC.2)(n) ⇒ ∂_n` not iso — F18 gives `δ_n ≠ 0` for all `n`); F17 Thm 5.1 + Cor 5.1 ⟹ `H̃^k(Δ_{n+1}) ≅ H̃^{k-1}(Δ_n)`, matching mg-6295 `B_3 = 2·sgn` and F14 `B_4 = 2·sgn`.
- **Route (ii)** closed-negative (F16). **Route (iii)** / mg-b345 PARKED — F18's escalation trigger is *definitively* unmet (the route-(iii) revisit was conditioned on the internal route *failing* to deliver (UCC); it has now delivered both halves — (UCC.1) via F17, (UCC.2) via F18).
- **Scope boundary** — F18 closes **(UCC.2)**, hence **(UCC)**, hence the **F10 cohomological core** (F10 parts (i)–(ii)). It does **not** address **(ICOP-step)** or the **width-3 reduction bridge** (F10 §7.4 — the secondary inputs of F10 part (iii)); those are outside (UCC) and outside F18's scope. Do not conflate "cohomological core unconditional" with "full numerical width-3 theorem unconditional" — the latter still rests on those two `n ≤ 6`-verified inputs.
- Trust-surface impact: none. No new axioms, no Lean changes, no HPC.

---

## §4. References

- mg-4d3a (F17) — `docs/compatibility-geometry-F17-equivariant-cofiber-morse.md`, `docs/state-F17.md`, `scripts/compat_geom_F17_equivariant_morse.py`. GREEN-equivariant-uniform. §5 (Theorem 5.1 — `(UCC.1) ⟺ Hyp(n)`, `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)`), §7.3 (**the (UCC.2) handle — F18's mandate**), §8.3 (**F18 recommended — attack `ι_n` directly**). **Parent.**
- mg-8216 (F10) — `docs/general-n-proof-synthesis.md`, `docs/state-F10.md`. GREEN-conditional. §6.2 (the inductive step), §6.3 (**(UCC)**), §6.7 (the conditional theorem), §7.3–§7.4 ((ICOP-step) + width-3 bridge — the secondary inputs of part (iii); the recommended next targets after F18).
- mg-59f3 (PCR-2 / F8″″) — `(UCC.2)` at `n = 3`. F18 recovers it by the non-circular route (D1 §4.2); the original used `H̃^1(Δ_4) = 0 = Hyp(n+1)`.
- mg-f893 (F16) — `docs/compatibility-geometry-F16-central-stability-presentation.md`. AMBER-route-ii-stalls. §5 ((UCC.2) independent of route (ii) — F18 confirms: (UCC.2) is unconditional).
- mg-8355 (F15) — `docs/compatibility-geometry-F15-e2-partial-test.md`. AMBER-partial3-not-iso. §4 (the circular-for-general-`n` `n=3` route), §6 (`∂_n` iso ⟺ `δ_n = 0`).
- mg-3839 (F14), mg-6295 (PCR-Lit-2 / M1) — `B_4 = 2·sgn_{S_4}`, `B_3 = 2·sgn_{S_3}`; recovered by Cor. 5.1 + F17.
- mg-ecf6 (F13) — good-pair / pair-LES conventions. mg-b352 (F11) — routes (i)/(iii). mg-b345 (F8″) — route (iii), PARKED.
- Björner 1995 (*Topological methods* §10 — the order-homotopy lemma); Kozlov 2008 (*Combinatorial Algebraic Topology* Ch. 10 — the prism operator); Quillen 1973 (§1.3 — comparable poset maps homotopic); Hatcher 2002 (§2.1–2.2 — the prism, the LES of a good pair, homotopy invariance).

---

*Cumulative state doc for mg-d039 (F18). Session 1 DONE — verdict GREEN-ucc2-proven. Branch `polecat-cat-mg-d039`. `ι_n : Δ_n ↪ Δ_{n+1}` is null-homotopic for every `n ≥ 3` (explicit `S_n`-equivariant poset zig-zag `ι_n ≤ κ_n ≥ const_{ω_n}`, unconditional), so `δ_n` is injective: **(UCC.2)** holds for all `n`. With F17 ((UCC.1) ⟺ Hyp(n)), **(UCC) is COMPLETE** and the **F10 cohomological core is UNCONDITIONAL**. The numerical width-3 conclusion additionally rests on (ICOP-step) + the width-3 bridge (F10 §7.4) — the recommended next targets. Route (ii) stays closed; route (iii) stays parked (escalation definitively unmet). No new axioms; no Lean changes.*
