# OneThird L1b arc — DRIFT AUDIT: `spectral_near_ordinal_sum_program.tex` vs what was built

**Work item:** mg-c899 (PRIORITY-1, Daniel-commissioned, vision-critical). Pure audit — **no
math changed, continued, or extended**. Deliverable: a crisp verdict + per-question findings.

**Baseline read (the authority):**
`/Users/daniel/Library/Mobile Documents/com~apple~CloudDocs/spectral_near_ordinal_sum_program.tex`
(603 lines, read in full, readable). Anti-drift protocol `~/.pogo/agents/pm/anti-drift-protocol.md`
and `docs/OneThird-Algebraic-Program-Vision.md` cross-referenced.

**Built docs audited:** `docs/OneThird-L1b-ExpectedRank-Certificate.md` (mg-8201, `6a4abec`),
`docs/OneThird-L1b-Spread-Locality.md` (mg-dbd1, `8efdac4`), `docs/OneThird-L1b-Bwall-state.md`
(mg-2acf `3692f35` + mg-9de3 `e04d92b`).

---

## VERDICT: **DRIFTED — partially, and diagnosably.** Premise narrowed at mg-8201; math is width-mixed.

**Headline.** The baseline `.tex` targets a **general, any-width** minimal counterexample. The
L1b certificate arc silently narrowed the premise to **width-3** at its very first doc (mg-8201),
inheriting the repo's standing `one_third_width_three` scope. That narrowing was **never
authorized by the `.tex` program** — it is not silent-hidden (every built doc says "width 3" out
loud) but it is silent-*unflagged-against-the-.tex* (no doc checks itself against the general
program's scope; the "vision checks" in mg-2acf/mg-9de3 check against the *width-3* M1 target and
the *algebraic-program* pivot, never against the `.tex`'s general minimal counterexample).

**But the drift is not uniform across the arc's two load-bearing pieces:**

- **(A) SPREAD `‖r‖² = Ω(n³)` — ON-TRACK / fully general.** Proven using **only** `δ < 1/3` (the
  frozen hypothesis H). The built doc states explicitly (`Spread-Locality.md` §1.3): *"No width
  hypothesis. The proof uses only (H)… Width 3 is a special case."* Directly reusable for the
  general program with zero rework.
- **(B) LOCALITY `E[Σdisp²] = O(E[inv_e])` — DRIFTED to bounded width.** The reduction that kills
  the cross term (Dilworth split of `Inc(x)` into `≤ 2` chains + Cauchy–Schwarz) is
  **width-3-load-bearing as written**, and the empirical searches + the stated verdicts are all
  width-3. It does **not type-check for an unbounded-width** minimal counterexample (the constant
  is `w−1 = Θ(n)` when `w = Θ(n)`). *However*, the built doc itself flags the reduction is
  **width-parametric** (works for any fixed `w`) and the surviving **residual is
  width-independent** — so the specialization is a bounded-width crutch, not an irreducible
  width-3 fact.

**Net.** Closing L1b **as built** would prove `λ_std ≥ 1 − O(1/n)` for **bounded-width** (canonically
width-3) frozen counterexamples. It would **not** settle the general minimal counterexample the
`.tex` describes. The gap between "as built" and "the program" is **one specific step** — the
per-element `≤ 2`-chain Cauchy–Schwarz bound in (B) — not the whole arc. (A) and the per-chain
residual are already width-agnostic.

---

## Q1. PROGRAM SCOPE — what does the `.tex` actually target?

**General any-width minimal counterexample. No width bound anywhere.** Verbatim scope language:

- §1, line 51: *"Let `P` be a finite poset on the ground set `[n]={1,…,n}`."*
- §1, Definition 1.2 (line 71–75): *"A counterexample is a poset `P` satisfying `δ(P)<1/3`."*
  (No width qualifier.)
- §1, lines 82–86: *"The programme below assumes that a minimal counterexample can be labelled so
  that `e = 12⋯n`."* — the only structural assumption is the **distinguished order**, not a width.
- Confirmed mechanically: **`grep -i width` over the entire 603-line `.tex` returns NOTHING**;
  so do `dilworth`, `antichain`, `width three`. The program never invokes width at all.

**Does the program chain assume a width bound?** No. Walking the boxed architecture
(`.tex` §14, lines 486–528): *minimal counterexample → bad mixing → `λ_std ≈ 1` → low-conductance
prefix → near ordinal sum → balanced pair by minimality.* Every link is width-agnostic:
- The symmetrized Cayley walk `S_P`, the transport-energy identity (Prop. §4), the standard-block
  quotient, and `λ_std` are defined for **any** finite poset (§2–§7).
- The four main open lemmas L1–L4 (§16, lines 556–570) — porting, monotonicity/prefix, prefix
  Cheeger, near-ordinal-sum stability — are all stated for a general `P`. **Width never appears in
  any L-lemma.**

The `.tex` has **L1–L4**, not "L1b." The arc's "L1b" is a sub-target of **L1** (the porting lemma:
*bad BK mixing ⟹ `λ_std ≥ 1−ε`*), reframed by mg-8201 as a **direct** transport-certificate route
(certify `λ_std ≈ 1` via the expected-rank test vector `r = T_P u`, bypassing BK entirely). That
reframing is legitimate and on-program; the width narrowing is a *separate* issue layered on top.

## Q2. BUILT SCOPE — is the L1b machinery width-3-specific?

**Piece-by-piece, with load-bearing width-3 uses named:**

| Built component | Where | Uses width 3? |
|---|---|---|
| **Premise** ("minimal counterexample `P`") | `ExpectedRank-Certificate.md` §0 line 44–45 | **YES — narrows the premise.** Verbatim: *"a hypothetical minimal counterexample `P` (**width-3**, `δ(P)<1/3`, every incomparable pair frozen…)"*. The `.tex`'s general `P` becomes width-3 here, at the arc's first doc. |
| **(A) SPREAD** `‖r‖²=Ω(n³)` | `Spread-Locality.md` §1 | **NO.** §1.3 verbatim: *"No width hypothesis. The proof uses only (H)… Width 3 is a special case."* Band bound `(2/3)k ≤ d_k ≤ (2/3)k+(n−1)/3` uses only per-pair `δ<1/3`. |
| **(B) cross-term elimination** | `Bwall-state.md` §1–2 | **YES — load-bearing.** §1 verbatim: *"If `a,b,c ∈ Inc(x)` were pairwise incomparable then `{x,a,b,c}` is a 4-antichain, contradicting width 3. Hence `Inc(x)` has width ≤ 2, and by **Dilworth** splits into **at most two chains** `Y, Z`."* Then `(S_Y+S_Z)² ≤ 2(S_Y²+S_Z²)` (constant **2** = number of chains) removes the cross term. |
| **(B) width-parametric note** | `Bwall-state.md` §2 parenthetical | **Generalizes.** Verbatim: *"This works for any fixed width `w`: `Inc(x)` splits into `≤ w−1` chains and the constant is `w−1`. Width 3 gives constant 2; the residual per-chain question is **width-independent**."* |
| **(B) per-chain residual** (block-cross non-realizability / `E[S_C²]=O(E|S_C|)`) | `Bwall-state.md` §4, S2 | **NO (intrinsically).** The residual is a single-element-vs-single-chain second-moment statement; §4 verbatim: *"the residual per-chain question is width-independent."* All *empirical* probing of it (`n≤9`/`n≤13`, 20 000 dense trials) is done in width-3, but the *statement* is not width-bound. |
| **Empirical searches, verdicts** | all three docs, `scripts/*` | **YES (framing).** Every random search, growth curve, and "for every width-3 frozen counterexample" verdict (`Spread-Locality.md` §5, `Bwall-state.md` S2) is width-3. |

**Would (A) spread/locality type-check for a general-width minimal counterexample?**
- **(A): yes, unchanged.** Uses only `δ<1/3`.
- **(B): no, as written.** The Cauchy–Schwarz step splits `disp_σ(x)` over `w−1` chains and pays a
  constant `w−1`. For an unbounded-width minimal counterexample (`w` can be `Θ(n)`), that constant
  is `Θ(n)` and the reduction `Cross ≤ (w−1)·Σ_x(E[S²]…)` **loses a factor `Θ(n)`** — it no longer
  delivers `O(E[inv_e])`. So (B)-as-built is a genuinely **bounded-width** statement; width-3 is
  the canonical instance, but the essential requirement is `w = O(1)`, which a general minimal
  counterexample need not satisfy.

## Q3. DRIFT VERDICT — advance the program, or settle only the special case?

**Closing L1b as built settles the BOUNDED-WIDTH (canonically width-3) special case, not the
general program the `.tex` describes.** Concretely: with (A)+(B)+`Λ=O(1)` all closed, the
certificate yields `1−λ_std ≤ ½Λ²·E[Σdisp²]/Ω(n³) = O(E[inv_e]/n³) = O(1/n)` — but the `E[Σdisp²]`
control (B) holds only when `Inc(x)` splits into `O(1)` chains, i.e. bounded width. So the arc
would prove the `.tex`'s **L1 (porting/certification) lemma for bounded-width posets** and leave
the general-width case — the case the program is *about* — untouched at exactly the (B) step.

**WHERE/WHEN the narrowing happened.** At **mg-8201 (commit `6a4abec`), the arc's very first doc**,
in the premise: `ExpectedRank-Certificate.md` §0 line 44–45 defines "minimal counterexample" as
"**width-3**, `δ(P)<1/3`, …". The baseline `.tex` has no width there. The subsequent docs inherited
this premise: mg-dbd1 kept (A) general anyway (good instinct, §1.3) but stated the payoff "for
every width-3 frozen counterexample" (§5); mg-2acf/mg-9de3 made width-3 **operationally
load-bearing** in (B) via the Dilworth `≤2`-chain split.

**Authorized or silent?** **Silent — against the `.tex`.** No built doc checks its scope against
`spectral_near_ordinal_sum_program.tex`. The width-3 came from the **repo's standing scope**
(`one_third_width_three`) and from mg-8201's predecessor chain (mg-b0a6 etc.), which were all
width-3. It was *visible* (never hidden — every doc says "width 3") but *unauthorized* relative to
the general program: the `.tex` is Daniel's newer, broader statement, and nobody ran a stage-4
"does this match the vision doc" check against it. This is precisely the anti-drift protocol's
named failure mode (§"Why this exists": *"the central thing… was assumed to match the
vision/target, and the assumption was checked only LATE"*) — here the "central thing" is the
**scope/width of `P`**. The mg-2acf and mg-9de3 "vision checks" ran against the width-3 M1 target
and the algebraic-program pivot hinge, **not** against the general `.tex`, so they could not catch
this drift by construction.

**One-paragraph justification.** The program is width-agnostic by explicit construction (Q1). The
arc's foundational premise silently added width-3 (Q3-where), and one of its two load-bearing
lemmas, (B), was then proved via a tool (`Inc(x)` → `≤2` chains) that is genuinely bounded-width
(Q2). Therefore a completed L1b-as-built is a theorem about bounded-width counterexamples, and the
general minimal counterexample — the object the `.tex` exists to contradict — is not covered at the
(B) step. That is drift: valid-on-its-own width-3 mathematics standing in for a general-program
lemma. It is *partial* drift (not a wholesale wrong turn) because (A) and the (B)-residual are
already general, and the width-3 crutch is localized to one Cauchy–Schwarz inequality.

## Q4. GENERAL-PROGRAM VERSION — what would any-width L1b require, and is the work reusable?

The general L1b = *bad mixing ⟹ `λ_std(P) ≥ 1−O(1/n)`* for a general minimal counterexample.
Via the same certificate scaling law `1−R(r) = energy(r)/‖r‖²`, it needs the same two factors:

- **(A) SPREAD `‖r‖²=Ω(n³)`: already general — reuse verbatim.** No rework. (This is also the
  `.tex`'s own L2/monotone-standard-mode content in its weaker spread form.)
- **(B) LOCALITY `E[Σdisp²]=O(E[inv_e])` at general width:** the per-element `≤2`-chain
  Cauchy–Schwarz must be **replaced**. Options (all width-agnostic):
  1. A **global chain-counting / exchange** bound on `Σ_x E[disp²]` that does not decompose each
     `Inc(x)` into `O(1)` chains — the built doc already points here (`Bwall-state.md` §4: *"a
     **global counting/exchange attack** on this residual… is the natural next move"*). The
     per-chain residual object (`E[S_C²]=O(E|S_C|)` per frozen chain) is **width-independent and
     directly reusable**; what must change is aggregating it across a *global* set of chains rather
     than `≤2`-per-element.
  2. A separate structural theorem that **minimal counterexamples are bounded-width** — not known,
     and if it existed the whole program would already be near-settled, so this is not a shortcut.
  3. A width-free handle on the Diaconis–Graham L2-vs-L1 gap (`E[Σdisp²]` vs `E[Σ|disp|]≤2E[inv_e]`)
     that never splits `Inc(x)` at all.

**Is the width-3 work a detour?** **Mostly reusable, one crutch to swap.** (A) transfers whole; the
per-chain second-moment residual (the actual hard content, block-cross non-realizability) is
already stated width-independently and was probed/sharpened by mg-2acf/mg-9de3; the *only*
width-3-specific piece is the "≤2 chains per element ⇒ constant-2 Cauchy–Schwarz" aggregation,
which a global chain count replaces. So the arc bought genuine general-program progress (A + the
residual's precise naming) alongside one bounded-width shortcut. It is **not** a wholesale detour.

## Q5. FORK RE-FRAMING — is "certificate route vs algebraic-program pivot" the right framing?

**No — the fork as posed is incomplete, and both of its arms are themselves width-3-scoped, so it
does not even address Daniel's "not just width 3" concern.**

- The mg-9de3 "RED-PIVOT" fork is *continue the certificate route* **vs** *pivot to
  `project_onethird_algebraic_program_vision`*. But `OneThird-Algebraic-Program-Vision.md` part 4
  is **itself width-3**: *"a poset `P` with `Q(P) < 1/3` **in width 3** would refute the
  conjecture."* So pivoting to the algebraic program does **not** de-narrow — it stays width-3.
  The general-width `.tex` program is the **only** any-width object on the table, and the fork
  **drops it entirely**. That is the real problem the drift audit surfaces.

- **The missing third option: RE-SCOPE L1b to the general program.** Keep (A) (already general),
  and replace the (B) `≤2`-chain crutch with the **global chain-counting** attack the built docs
  already recommend (Q4 option 1). This is neither "abandon the spectral certificate" nor "pivot to
  algebraic search" — it is *finish the same certificate at the width the `.tex` actually targets*.
  The residual becomes width-independent (already is), and closing it would advance the **general**
  program, not a special case.

**Plainly, for the PM/owner decision:**

1. **The `.tex` program is any-width; the L1b arc drifted to width-3 at mg-8201.** (A) is safe and
   general; (B) is bounded-width via one Cauchy–Schwarz step.
2. **The go/no-go fork Daniel was handed is mis-framed:** it pits certificate-continue against an
   algebraic pivot that is *also* width-3, silently retiring the only general program.
3. **Three real options, not two:**
   - **(a) Re-scope L1b general** (recommended if the spectral program is the vision): reuse (A),
     re-attack (B) via a global chain count — the width-3 residual work is a down-payment, not a
     sunk detour.
   - **(b) Accept width-3 as the arc's honest scope** and continue the certificate route as a
     width-3 result (consistent with the repo, but *acknowledge it no longer matches the general
     `.tex`* — a scope amendment, per anti-drift §"amendment rule").
   - **(c) Pivot to the algebraic-objects program** — a genuinely different vision
     (counterexample *search*, not the spectral *proof*), and note it is *also* width-3, so it does
     not resolve the "not just width 3" concern either.
4. **Whichever is chosen, the `.tex` scope and the width-3 narrowing should be recorded** in the
   vision docs (they currently are not), so the next checkpoint checks against the *general*
   program, not the width-3 inheritance.

---

## Appendix — audit trail (verbatim pointers)

- **Baseline general scope:** `.tex` §1 line 51 (`finite poset on [n]`), Def 1.2 line 71–75
  (`δ(P)<1/3`, no width), §16 lines 556–570 (L1–L4, no width). `grep -i width` over 603 lines: 0 hits.
- **Where width-3 entered:** `ExpectedRank-Certificate.md` §0 line 44–45 (premise "width-3"),
  commit `6a4abec` (mg-8201) — the arc's first doc.
- **(A) declared width-free:** `Spread-Locality.md` §1.3 ("No width hypothesis").
- **(B) width-3 load-bearing:** `Bwall-state.md` §1 (Dilworth `≤2` chains from "4-antichain
  contradicts width 3"), §2 (constant-2 Cauchy–Schwarz).
- **(B) width-parametric + residual width-independent:** `Bwall-state.md` §2 parenthetical, §4.
- **Global-count next-move already flagged:** `Bwall-state.md` §4 ("global counting/exchange
  attack… natural next move"), §7 rec 1.
- **Algebraic pivot is also width-3:** `OneThird-Algebraic-Program-Vision.md` part 4 line 16.
- **Anti-drift stage-4 (vision validation) never run against the `.tex`:** the mg-2acf/mg-9de3
  "vision checks" reference the width-3 M1 target and the algebraic-program hinge, not
  `spectral_near_ordinal_sum_program.tex`.

*Audit only. No math continued, fixed, or extended. Baseline `.tex` was readable and is quoted, not
summarized-as-substitute.*
