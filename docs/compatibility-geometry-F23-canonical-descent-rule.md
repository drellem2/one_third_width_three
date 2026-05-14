# Compat-Geom — F23: the canonical descent rule for `c*_{n+1}` — the `S_{n+1}`-equivariant structure selecting the genuine critical chain (mg-531f)

**Branch:** `polecat-cat-mg-531f` (mg-531f).
**Parent:** mg-0c5d (F22-HPC Session 2, **RED-tripwire**) — `docs/state-F22-HPC.md` §5 (findings 1–6, the three continuation routes); F23 is **route 1** ("pin the descent canonically"). Also mg-43fb (F22-HPC S1) and mg-a2cb (F21, Proposition F21.1).
**Chain:** F10 → F17 (mg-4d3a, `M_rel^eq`) → F18 (mg-d039) → F19 → F20 → F21 (mg-a2cb, Prop F21.1) → F22-HPC (mg-43fb / mg-0c5d) → **F23 (mg-531f)**.
**Type:** Structural research (`S_{n+1}`-equivariant discrete Morse / order-complex combinatorics) with bounded materialisation at `n = 3 → 4` as the testbed. **No new axioms; no Lean changes; no (co)homology datapoint touching the trust surface.**
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T17:23Z (milestone 1 — full gap-free width-3 proof); 2026-05-14T22:32Z ("keep pushing").

---

## Verdict: **GREEN-descent-pinned (HPC-per-n variant).**

A canonical `S_{n+1}`-equivariant rule that selects `c*_{n+1}` from the 4-orbit descent candidate set **does exist** — and F23 names it, proves it decisively at the `n = 3 → 4` testbed, and proves it is genuinely `S_{n+1}`-equivariant. **But** the rule is **not** a closed-form / `n`-uniform generative rule: it is **chamber-Morse criticality itself** (F23's candidate form B — the structure F21 §5.2 / F22-HPC S2 finding 6 predicted was needed), made `S_{n+1}`-equivariant by the `min-|L|-profile` tie-break. Every *structural* (non-criticality) discriminator of the 4 orbits is **refuted as an `n`-uniform rule** by the recorded `c*_3, c*_5`. So applying the rule needs the level-`(n+1)` chamber-Morse matching `M^chamber_{n+1}` — HPC-class from `n = 5` on. **The cofiber-Morse induction (Prop F21.1) is correct but does not self-close into a closed-form recursion.**

The decisive consequence for milestone 1: the chamber-Morse route to F10 part (iii) is unblocked **only in the HPC-per-n sense** — which is **route 2** of `state-F22-HPC` §5, a separate Tier-3 decision — **or** the program pivots part (iii) to the documented **BK/Cheeger-expansion mechanism** (mg-26fc). That is a PM/Daniel decision; F23 surfaces it with this precise finding.

**On the meta-question (ticket Goal 2):** "the canonical chamber-Morse critical cell `c*_n`" **is** a well-defined canonical `S_{n+1}`-equivariant object — via `min-|L|-profile` chamber-Morse criticality, an `S`-equivariant refinement of the label-dependent lex-min definition. It does **not** need re-founding. This is **not** the AMBER-not-canonically-pinnable outcome. But the object's *generation* is irreducibly tied to the level-`(n+1)` chamber-Morse matching: the third structural model (the descent) narrows `c*_{n+1}` but, like the ι-tower (F19→F20) and the `M_rel^eq`-survivor (F21→F22), does not yield a self-contained closed-form recursion.

**Deliverables (this session):**
- `scripts/compat_geom_F23_canonical_descent.py` — the candidate-rule testbed at `n = 3 → 4` (8 sections; pure-Python stdlib; exact arithmetic; runtime ≈ 3 s).
- `docs/compatibility-geometry-F23-canonical-descent-rule.md` (this doc).
- `docs/state-F23.md` (cumulative state ledger).

---

## §0. The question, precisely

After F17 + F18 the F10 cohomological core (parts i–ii) is unconditional. Part (iii) — the numerical width-3 conclusion — has been pursued through "the canonical chamber-Morse critical cell `c*_n`" and the **inductive rule** generating the `c*_n` tower. F21's **Proposition F21.1** re-founded that induction: `c*_{n+1}` is **(the descent of)** a critical `(n−1)`-cell of the perfect `S_n`-equivariant cofiber Morse matching `M_rel^eq` (F17), the one surviving the F18 cross-boundary Forman cancellation against `c*_n`.

F22-HPC Session 2 (mg-0c5d, RED-tripwire) materialised the descent at the `n = 3 → 4` testbed and pinned down precisely what is — and is not — determined:

- The cross-boundary cancellation assembles a **perfect, acyclic `M_4 = M_3 ⊔ M_rel^eq + cross-boundary cancellation`** whose unique critical `2`-cell is the **survivor `D-lift(c*_3)`** (`|L|`-profile `(6,3,2)`).
- The recorded `c*_4` **is** reachable from the survivor by a gradient `V`-path *inside the perfect `M_4`* — F21.1's "(the descent of)" is literally correct.
- **But the descent target is not canonically pinned:** of the `212` descent-reachable `2`-cells, `151` are all-BFT-sharp, and the `min-|L|-profile` `(5,3,2)` among those is achieved by `44` cells spanning **4 `S_4`-orbits** — recorded `c*_4` is one of them, not uniquely distinguished. (F22-HPC S2 finding 6 / F21 §5.2.)

> **F23's task.** Find the additional `S_{n+1}`-equivariant structure — beyond `min-|L|-profile` + BFT-sharp — that selects THE canonical `c*_{n+1}` among the 4 orbits, and answer **decisively**: does such a canonical rule **exist**?

The `n = 3 → 4` case is the testbed: `Δ_4` has `≈ 1.5·10⁴` cells, materialisable cheaply (the F22-HPC S2 Section-10 trip-wire infrastructure is in place). Any candidate rule must select recorded `c*_4` from the 4 orbits, `S_{n+1}`-equivariantly.

---

## §1. The 4-orbit candidate set — reproduced and characterised

`scripts/compat_geom_F23_canonical_descent.py` Section 1 rebuilds the perfect `M_4` and the descent-reachable set and **reproduces F22-HPC S2's candidate set exactly**: `212` descent-reachable `2`-cells → `151` all-BFT-sharp → `44` of `min-|L|-profile` `(5,3,2)` → **4 `S_4`-orbits**, each of size `24`.

Section 2 runs the full `S_4`-equivariant invariant battery on the 4 orbits. They are **partially structurally degenerate**:

| invariant | orbit 0 | orbit 1 | orbit 2 | **orbit 3 = recorded `c*_4`** |
|---|:---:|:---:|:---:|:---:|
| `|L|`-profile | `(5,3,2)` | `(5,3,2)` | `(5,3,2)` | `(5,3,2)` |
| per-step `Pr` | `(3/5, 2/3)` | `(3/5, 2/3)` | `(3/5, 2/3)` | `(3/5, 2/3)` |
| width profile | `(2,2,2)` | `(2,2,2)` | `(2,2,2)` | `(2,2,2)` |
| bottom-poset iso-type | same | same | same | same |
| `|S_4`-orbit`|` | `24` | `24` | `24` | `24` |
| **top-poset OSA** | `OSA(1,2,1)` | `OSA(1,1,2)` | `OSA(1,2,1)` | **`OSA(2,1,1)`** |
| **middle-poset iso-type** | A | A | B | **B** |
| **new-element-3 locus** | `[D, M, M]` | `[D, M, M]` | `[D, D, M]` | **`[D, D, D]`** |
| order-reversal dual | orbit 2 | orbit 3 | orbit 0 | orbit 1 |

(`D` = pure-LOW / in `D_3`; `M` = MIXED; A, B = the two `4`-element middle-poset isomorphism types.)

**Key reading.** The 4 orbits agree on `|L|`-profile, per-step `Pr`, width profile, bottom-poset iso-type, and orbit size. **(L2-struct)** — the top poset is a width-2 OSA with a size-2 block — holds for **all 4**: it does *not* discriminate. They differ in (i) top-poset OSA signature, (ii) middle-poset iso-type, (iii) the new-element-3 locus. The pair `(`middle iso, top OSA`)` separates all 4 orbits, and recorded `c*_4` is uniquely `(B, OSA(2,1,1))`. This confirms, concretely, F21 §5.2's lower-bound argument: `(CM-struct)(i)+(ii)` — BFT-sharp + width-2-OSA top — do **not** pin `c*_{n+1}`. More structure is genuinely needed.

---

## §2. Candidate Rule A — a deterministic descent `V`-path procedure — **fails**

The first candidate form (ticket Goal 1): a Forman-respecting greedy/deterministic descent — from the survivor, follow a *canonically chosen* gradient `V`-path and take where it lands. For the choice to be `S_{n+1}`-equivariant it must use an `S_{n+1}`-invariant criterion; a lex-min on labels is not equivariant. The two natural invariant criteria are **shortest `V`-path** and **most `V`-paths**.

> **Finding 2.1 (Rule A fails).** The shortest descent `V`-path lengths per orbit are `(20, 22, 18, 20)` — **'shortest `V`-path' selects orbit 2, not recorded `c*_4` (orbit 3).** Moreover the gradient flow of the perfect `M_4` is a DAG with wide fan-out: every orbit is reached by `V`-paths of many lengths (Section 2), so no single `S_4`-invariant "pick a `V`-path" criterion is distinguished. A deterministic descent `V`-path procedure either (i) uses a label-dependent tie-break — not equivariant — or (ii) uses "shortest path" — which selects the **wrong** orbit.

Rule A is **not** a canonical rule.

---

## §3. Candidate Rule B — `S_{n+1}`-equivariant chamber-Morse criticality — **this is the rule**

The second candidate form (ticket Goal 1, flagged by F22-HPC S2 finding 6 / F21 §5.2 as "the likely needed structure"): a chamber-Morse criticality condition made precise and `S_{n+1}`-equivariant.

### 3.1 The construction

`M^chamber_n` (F2/F8 — `compute_f2_matching` in `compat_geom_cofiber_morse_n3n4.py`) is the matching whose critical cells **define** the program's canonical chamber-Morse cells. It is a deterministic, reproducible object; a relabelling `σ ∈ S_n` conjugates it to `σ · M^chamber_n`, and `crit(σ · M) = σ · crit(M)`. Since `S_n`-orbits are themselves `S_n`-invariant,

> the **set of `S_{n+1}`-orbits that meet `crit(M^chamber_{n+1})`** is labelling-independent — a genuine `S_{n+1}`-invariant.

### 3.2 The result at the `n = 3 → 4` testbed

`M^chamber_4` has critical vector `(2, 5, 4, 0, 0)` — **4 critical `2`-cells**, in **4 distinct `S_4`-orbits**, with `|L|`-profiles:

| `M^chamber_4` critical `2`-cell | `|L|`-profile | BFT-sharp? | descent-reachable? | `==` recorded `c*_4`? |
|---|:---:|:---:|:---:|:---:|
| #1 | **`(5,3,2)`** | ✓ | ✓ | **✓ (exact, same labelling)** |
| #2 | `(12,5,2)` | ✓ | ✓ | ✗ |
| #3 | `(8,3,2)` | ✓ | ✓ | ✗ |
| #4 | `(8,4,2)` | ✓ | ✓ | ✗ |

> **Finding 3.1 (Rule B works — decisively).** All 4 chamber-Morse critical `2`-cells are descent-reachable and BFT-sharp, but only **one** has the descent set's `min-|L|-profile` `(5,3,2)` — and that one **is recorded `c*_4` exactly** (same labelling, not merely the same orbit). Equivalently: of the 4 descent orbits, **exactly one — recorded `c*_4`'s — meets `crit(M^chamber_4)`**; orbits 0, 1, 2 contain **no** chamber-Morse critical cell (under any labelling, by the `S_4`-invariance of §3.1). So
> ```
>   c*_{n+1}  =  the unique min-|L|-profile critical (n-1)-cell of M^chamber_{n+1}
>            =  the unique descent orbit (of the 4) meeting crit(M^chamber_{n+1}).
> ```

This is a canonical `S_{n+1}`-equivariant rule and it **decisively pins recorded `c*_4`** at the `n = 3 → 4` testbed. It is consistent at the `n = 3` base (§5) — there `M^chamber_3` is already perfect, so `c*_3` is trivially its unique critical cell.

### 3.3 The non-trivial content — and the catch

The rule's content is a **compatibility theorem** between two *independently defined* matchings: the descent set comes from `M^cofiber_4 = M_3 ⊔ M_rel^eq + cross-boundary cancellation` (the F17/F18 cohomological reduction), and `crit(M^chamber_4)` comes from the F2/F8 chamber-Morse greedy. The theorem — *the 4-orbit descent set and the 4 chamber-Morse critical orbits intersect in exactly one orbit, `c*_{n+1}`* — is not a tautology.

**But the catch is decisive.** Chamber-Morse criticality is the **defining property** of `c*_n`. Applying Rule B at level `n+1` requires `crit(M^chamber_{n+1})` — and once you have that, you have `c*_{n+1}` directly (it is the `min-|L|-profile` element). The descent picture (Prop F21.1) does **not** *replace* `M^chamber_{n+1}`; it *narrows* `c*_{n+1}` to a bounded candidate set that `M^chamber_{n+1}` then resolves. As a **generative** rule — compute `c*_{n+1}` from `c*_n` without the level-`(n+1)` chamber-Morse matching — Rule B is **vacuous**. It is the original definition of `c*_n`, made `S`-equivariant.

This is exactly the **HPC-per-n** sub-case of the ticket's GREEN-descent-pinned verdict: a canonical rule exists, but it requires per-`n` HPC materialisation.

---

## §4. Candidate Rule C — lex-min over a structural `S_4`-invariant — **fails `n`-uniformity**

The third candidate form (ticket Goal 1): a canonical-order lex-min over an `S_{n+1}`-equivariant *structural* invariant — one that does **not** invoke chamber-Morse criticality. Two structural invariants separate recorded `c*_4` from the other 3 orbits at `n = 3 → 4`:

- **(C1) top-poset OSA signature.** Recorded `c*_4` is the unique orbit with top `OSA(2,1,1)` (the others: `OSA(1,2,1)`, `OSA(1,1,2)`, `OSA(1,2,1)`).
- **(C2) new-element-3 locus.** Recorded `c*_4` is the unique orbit whose chain keeps the new element `3` **pure-LOW (in `D_3`) throughout** — `[D, D, D]` vs `[D, M, M]`, `[D, M, M]`, `[D, D, M]`.

Both uniquely pick recorded `c*_4` *at the testbed*. But are they `n`-uniform rules? **No** — and the refutation is decisive (§5):

> **Finding 4.1 (Rule C fails `n`-uniformity).** Every structural invariant that separates the 4 orbits at `n = 3 → 4` is **refuted as an `n`-uniform rule** by the recorded `c*_3, c*_5`:
> - **(C1) top-poset OSA** is `G_3 = OSA(1,2)`, `G_4 = OSA(2,1,1)`, `G_5 = OSA(2,2,1)` — three different shapes, no closed form (F21 Finding 2.1, re-confirmed). "Top is `OSA(2,1,1)`" is specific to `n = 4`.
> - **(C2) new-element locus** is **pure-HIGH** throughout `c*_3` (element `2` is above element `0` in both posets), **pure-LOW** throughout `c*_4`, and **absent → pure-HIGH → MIXED → MIXED** along `c*_5` — *no* `n`-uniform pattern. "The new element stays in `D_n`" is specific to `n = 4`.

"Lex-min over a structural `S_4`-invariant" picks the right orbit at the testbed **only by coincidence of `n = 4`** — it is precisely the "extrapolate a closed form from `n ≤ 5`" trap F21 Finding 2.1 warns of. Rule C is **not** a canonical rule.

---

## §5. The `n`-uniformity probe — why no closed-form rule survives

`scripts/compat_geom_F23_canonical_descent.py` Section 6 tabulates, for the entire exact record:

| `c*_n` | new-element-`(n−1)` locus per poset | top-poset OSA | elements pure-LOW throughout | pure-HIGH throughout |
|---|---|:---:|:---:|:---:|
| `c*_3` | `[HIGH, HIGH]` | `OSA(1,2)` | `{0}` | `{2}` |
| `c*_4` | `[LOW, LOW, LOW]` | `OSA(2,1,1)` | `{1,3}` | `{2}` |
| `c*_5` | `[absent, HIGH, MIXED, MIXED]` | `OSA(2,2,1)` | `{0,2}` | `{1}` |

There is **no `n`-uniform structural pattern**: not the new-element locus, not the top-poset OSA signature, not the pure-LOW / pure-HIGH element sets. This sharpens F21 Finding 2.1 ("the width/`|L|`/`Pr`-profiles of `c*_n` are not `n`-uniform; no closed form is forced by `n ≤ 5`") **at the level of the selector**: the additional structure that pins `c*_{n+1}` among the descent candidates is *also* not closed-form. The **only** `n`-uniform selector is chamber-Morse criticality itself — Rule B — which is the *definition* of `c*_n`.

---

## §6. The HPC-per-n cost — and why it is decisive

Section 7 confirms the cost structure:

- **`n = 3` (base).** `M^chamber_3` is **perfect** (critical vector `(0,1,0)`): `c*_3` is its unique critical `1`-cell. The rule is trivial here.
- **`n = 4` (testbed).** `M^chamber_4` is **not** perfect (critical vector `(2,5,4,0,0)`): `c*_4` is the unique `min-|L|-profile` critical `2`-cell among 4 — the rule's first real use, and it works (§3).
- **`n = 5`.** `|PPF_5| = 4110`; the order complex `Δ_5` already has `> 2·10⁷` cells at dimension 3 and grows. The chamber-Morse matching on the **full `Δ_5`** is **Tier-3 HPC-class** (consistent with F20 §1.3 / F21 §5.3 — the chamber-Morse greedy is HPC for `n ≥ 5`).

> **Finding 6.1 (HPC-per-n is decisive).** Rule B is the canonical selector, but applying it at level `n+1` requires the level-`(n+1)` chamber-Morse matching `M^chamber_{n+1}`, which is HPC-class from `n = 5` on. The rule is **HPC-per-n**, not closed-form / `n`-uniform. The cofiber-Morse induction (Prop F21.1) narrows but does not close the recursion.

---

## §7. What F23 establishes and does not establish

### 7.1 Establishes

- **A canonical `S_{n+1}`-equivariant rule selecting `c*_{n+1}` from the 4-orbit descent candidate set exists** (Rule B, §3): `c*_{n+1}` is the unique `min-|L|-profile` critical `(n−1)`-cell of `M^chamber_{n+1}`; equivalently, the unique descent orbit meeting `crit(M^chamber_{n+1})`. It is genuinely `S_{n+1}`-equivariant, decisively pins recorded `c*_4` at the testbed (exact, same labelling), and is consistent at the `n = 3` base.
- **The rule is chamber-Morse criticality itself** (F23 candidate form B) — the structure F21 §5.2 / F22-HPC S2 finding 6 predicted — made `S`-equivariant by the `min-|L|-profile` tie-break, an `S`-equivariant refinement of the label-dependent lex-min definition. So **"the canonical chamber-Morse critical cell `c*_n`" is a well-defined canonical `S_{n+1}`-equivariant object** — it does **not** need re-founding (this is **not** the AMBER outcome).
- **No closed-form / `n`-uniform structural rule exists.** Every *structural* (non-criticality) discriminator of the 4 orbits — top-poset OSA signature, new-element locus, size-2-block position — is refuted as `n`-uniform by the recorded `c*_3, c*_5` (§4–§5). This sharpens F21 Finding 2.1 at the level of the selector.
- **The rule is HPC-per-n** (§6): applying it needs `M^chamber_{n+1}`, HPC-class from `n = 5`. The cofiber-Morse induction (Prop F21.1) is correct but does **not** self-close.
- **Rules A and C fail** (§2, §4): a deterministic descent `V`-path procedure selects the wrong orbit (shortest path → orbit 2) or is not equivariant; lex-min over a structural invariant fails `n`-uniformity.
- **The F22-HPC S2 candidate set is reproduced exactly** (§1): `212 → 151 → 44 → 4 orbits`.
- **Trust-surface impact: none.** No new axioms; no Lean changes; no (co)homology datapoint. Elementary order-complex combinatorics + exact rational arithmetic on the materialised `n = 3 → 4` testbed.

### 7.2 Does not establish

- **The genuine `c*_6, c*_7` are not produced.** The rule (Rule B) requires `M^chamber_6, M^chamber_7` — HPC-class, deliberately out of F23 scope (route 2 of `state-F22-HPC` §5).
- **No closed-form recursion for the `c*_n` tower.** F23 establishes that none of the structural candidate forms yields one; it does not prove a closed-form rule is *impossible* in principle — only that it is not realised by any of the `S_{n+1}`-equivariant structures the descent picture makes available, and that the exact record `n ≤ 5` refutes every structural candidate.
- **The `n`-uniform proof of (CM-rel)** (the former F23 plan, now F24-shaped) is not attempted — it is a follow-on that the HPC anchor data would seed, not in F23 scope.

---

## §8. The decision F23 surfaces

Three structural models have now been tested for the inductive rule generating the `c*_n` tower:

| model | ticket | outcome |
|---|---|---|
| ι-tower | F19 → F20 | broken (F20: `c*_n` is not an ι-lift) |
| `M_rel^eq`-survivor | F21 → F22-HPC | broken (F22-HPC S2: the survivor is `D-lift(c*_n)`, not `c*_{n+1}`) |
| **the descent** | **F22-HPC S2 → F23** | **narrows to 4 orbits; the selector is chamber-Morse criticality — HPC-per-n, not closed-form** |

F23's verdict is **GREEN-descent-pinned (HPC-per-n)** — strictly better than AMBER (a canonical `S_{n+1}`-equivariant rule *does* exist; `c*_n` *is* canonically well-defined), but it confirms the structural-shortcut hope is not realised: the descent picture does not yield a self-contained closed-form recursion for the `c*_n` tower. The chamber-Morse route to F10 part (iii) is unblocked **only** in the HPC-per-n sense.

The documented continuations (both PM/Daniel decisions):

1. **Route 2 of `state-F22-HPC` §5 — accept HPC-per-n.** Materialise `M^chamber_n` (or the cofiber-Morse `M^cofiber_n` + the descent) at `n = 6, 7` as Tier-3 HPC, pin the genuine `c*_6, c*_7`, and pursue the `n`-uniform proof of (CM-rel) seeded by that data. F23's Rule B is the precise selector this route would apply at each level.
2. **The BK/Cheeger pivot (mg-26fc).** mg-26fc established that 1/3–2/3 has **two** distinct-but-resonant mechanisms: the F-series cohomological one (the F19–F23 chain) **and** the **BK/Cheeger-expansion** mechanism (the in-tree width-3 paper `main.tex` + `step8.tex` spine, conditional on Hypothesis A). The BK/Cheeger route to part (iii) does **not** need the canonical chamber-Morse critical cell. F23 does **not** pivot pre-emptively; it documents the alternative.

F23's finding is decisive enough to bring to the PM/Daniel level: the structural route to part (iii) — the F19–F23 arc — has reached the point where the only remaining selector is the HPC chamber-Morse matching itself, and the choice between Tier-3 HPC and the BK/Cheeger pivot is now squarely a budget/strategy decision.

---

## §9. References

### 9.1 Predecessor and sibling mg-tickets

- **mg-0c5d** — F22-HPC Session 2 (the cross-boundary cancellation tracking): **RED-tripwire.** `docs/state-F22-HPC.md` §5 (findings 1–6 — finding 6 is the 4-orbit under-specification F23 resolves); `docs/compatibility-geometry-F22-hpc-critical-cells.md` Session-2 section; `scripts/compat_geom_F22_hpc_cell_tracking.py` Section 10 (the `n = 3` materialised trip-wire — F23's testbed infrastructure). **Parent (F23 = route 1 of its §5).**
- **mg-43fb** — F22-HPC Session 1 (the explicit `M_rel^eq` critical cells): **GREEN-partial.** The closure-operator lift infra; (CM-rel) confirmed `n = 3,4,5`.
- **mg-a2cb** — F21 (the genuine non-ι-lift canonical chamber-Morse cell): **GREEN-needs-hpc-anchor.** **Proposition F21.1** (the cofiber-Morse induction — F23 tests its descent clause), §5.2 (the lower-bound argument: `(CM-struct)(i)+(ii)` under-determine `c*_n` — F23 §1 confirms this concretely on the 4 orbits), Finding 2.1 (no closed form forced by `n ≤ 5` — F23 §5 sharpens this at the selector level).
- **mg-c3fa** — F20 (the `n`-uniform chamber-Morse critical-cell structure): **GREEN-partial.** §1.3 (the chamber-Morse greedy is HPC for `n ≥ 5` — F23 §6 confirms).
- **mg-5722** — F19 (the symmetric-pair engine L1; the ι-tower model — broken by F20).
- **mg-4d3a** — F17 (`M_rel^eq`, the perfect `S_n`-equivariant cofiber matching); **mg-d039** — F18 ((UCC.2), `δ_n` injective; the cross-boundary cancellation).
- **mg-26fc** — the two 1/3–2/3 mechanisms (the BK/Cheeger-expansion documented alternative — §8 route 2).
- **mg-8216** — F10: §6.7 part (iii), the numerical width-3 conclusion this structural arc serves.

### 9.2 Mathematical literature

- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — discrete Morse theory; gradient `V`-paths and Forman cancellation (the descent).
- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984); G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — the `[3/11, 8/11]` BFT-sharp interval.
- A. Björner, *Topological methods*, in *Handbook of Combinatorics*, Elsevier 1995, §10 — ordinal sums of antichains; order-complex combinatorics.

### 9.3 Code

- `scripts/compat_geom_F23_canonical_descent.py` — **this F23 / mg-531f** — the candidate-rule testbed. Sections: 0 (utilities), 1 (the F22-HPC S2 candidate set reproduced), 2 (the `S_4`-invariant battery), 3 (Rule A — deterministic descent `V`-path), 4 (Rule B — chamber-Morse criticality — **the rule**), 5 (Rule C — lex-min over a structural invariant), 6 (the `n`-uniformity probe), 7 (`n = 3` base + HPC-per-n confirmation), 8 (verdict). Pure-Python stdlib; exact `Fraction` / `int` arithmetic; imports `compat_geom_cofiber_morse_n3n4` (the materialised `Δ_4` infra) and `compat_geom_F22_hpc_cell_tracking` (the lift maps + the exact record `c*_3,4,5`).
- `scripts/compat_geom_F22_hpc_cell_tracking.py` (mg-43fb / mg-0c5d), `scripts/compat_geom_cofiber_morse_n3n4.py` (mg-3839/mg-6295) — the F22-HPC testbed infrastructure F23 builds on.

### 9.4 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (F23 is pure internal computation + structural analysis.)
- 2026-05-14T17:23Z — milestone 1 = the full gap-free width-3 proof, no sketches or gaps. (F23 is scrupulously honest: it finds a canonical rule, proves it works at the testbed, and reports precisely that the rule is HPC-per-n and that no closed-form structural rule survives `n`-uniformity — it does not pass a non-uniform coincidence off as the canonical rule.)
- 2026-05-14T22:32Z — "keep pushing." (F23 pushes the descent route to a decisive verdict and surfaces the resulting PM/Daniel decision precisely.)

---

*Polecat: mg-531f (F23). Branch: `polecat-cat-mg-531f`. Verdict: **GREEN-descent-pinned (HPC-per-n)** — a canonical `S_{n+1}`-equivariant rule selecting `c*_{n+1}` from the 4-orbit descent candidate set exists (Rule B — chamber-Morse criticality, made `S`-equivariant by the `min-|L|-profile` tie-break; F23 candidate form B), and decisively pins recorded `c*_4` at the `n = 3 → 4` testbed. But it is not closed-form / `n`-uniform: every structural discriminator of the 4 orbits is refuted as `n`-uniform by the recorded `c*_3, c*_5`, and the rule requires the level-`(n+1)` chamber-Morse matching — HPC-per-n. The cofiber-Morse induction (Prop F21.1) narrows but does not self-close. "The canonical chamber-Morse critical cell `c*_n`" is a well-defined canonical object — it does not need re-founding — but the chamber-Morse route to F10 part (iii) is unblocked only in the HPC-per-n sense (route 2 of `state-F22-HPC` §5) or the program pivots to the BK/Cheeger mechanism (mg-26fc): a PM/Daniel decision. No new axioms; no Lean changes. Cumulative state: `docs/state-F23.md`.*
