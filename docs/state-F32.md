# State F32 — Union-Closed → 1/3-2/3 bridge program (mg-c9d9) — cumulative state

**Ticket:** mg-c9d9 (F32-scope, scoping session). **Branch:** `polecat-cat-mg-c9d9`. **Parent:** Daniel reminder 2026-05-16T11:29:58Z articulating a 10-step proof program at `~/files/union_closed_1323_proof_steps.txt` to bridge from union-closed (Frankl-Holds via UC10+UC12+UC11+UC13+UC14 chain, all merged 2026-05-16) to 1/3-2/3 via canonical 3-antichain families. Cross-repo: the program *invokes* Frankl-Holds (which lives on `union_closed` repo) but lives on the 1/3-2/3 side (this repo, `one_third_width_three`).
**Type:** Multi-session F-series arc. Session 1 = scoping; Session 2 = F32-L4-α-lit (Phase 1.1 literature search); Session 4 = F32-width3 (per Daniel 14:33Z directive); execution sessions paused per Session 4 close recommendation.
**Status:** Session 4 (this entry) F32-width3 specialisation feasibility complete; F32 closure recommendation pending Daniel review.
**Verdict (after session 4):** **AMBER-mixed-Phase2-RED-binding — recommend close F32 per Daniel "on hold unless we learn more" directive (2026-05-16T14:33Z).** Session 1 AMBER-one-lemma-tractability-uncertain → Session 2 AMBER-L4-needs-scope-correction-before-derivation → Session 4 AMBER-mixed-Phase2-RED-binding (width-3 specialisation does NOT dissolve the L3 1/8-obstruction, which is structurally intrinsic to F(P) indexing by Q not L; Phase 1 L4 dissolution is partial via external Aires-Kahn input not F32-internal; Phase 3 L2 simplification absent). No execution sub-tickets recommended; Daniel's "on hold" directive should be respected.

---

## Session 1 — 2026-05-16 (scoping session, complete)

### Inputs read

- **`~/files/union_closed_1323_proof_steps.txt`** (full, 275 lines) — Daniel's 10-step proof program. Core objects: minimal counterexample `P`, strict canonical orientation `\ll`, 3-antichain canonical order, `S(Q) = \{A : Q \text{ orients } A \text{ canonically}\}`, family `F(P) = \{S(Q) : Q \ge P\}`. Steps 1–10 (setup → L1 → `F(P)` → L2 → Frankl → L3 → entropy bound → ERZ → L4 → contradiction). Four "Open Lemmas" labelled A/B/C/D (= L1/L2/L3/L4 in F32-scope's disambiguated naming).
- **F-series house-style references:**
  - `docs/compatibility-geometry-F31-phi-star-injectivity.md` (full §0 + §1, partial §2-§3) — recent RED verdict pattern; section-numbering conventions; cumulative-state-doc citing pattern.
  - `docs/compatibility-geometry-F30-chain-level-phi.md` (referenced for context).
  - `docs/compatibility-geometry-F29-cech-bias-cohomology.md` (referenced for context).
  - `docs/state-F29.md` (full session 1 entry) — cumulative-state-ledger format.
- **U1-dialect-collision baseline:** `docs/compatibility-geometry-structural-analogy-scoping.md` (mg-26fc) §4.4 (U1, U2, U3) — confirmed via F31 doc §4 references.

### Findings, ordered

#### F32.1 — Phase A: numerical-constants verify exactly (GREEN)

- `\Delta_{\mathrm{can}} = \log_2 6 - [1 + \tfrac{1}{2}\log_2 5] = 0.4239984533\ldots \approx 0.42400` bits (verified by direct arithmetic; matches Daniel's quoted `\approx 0.424`).
- `\Delta_{\mathrm{ERZ}} = \log_2(4/3) = 2 - \log_2 3 = 0.4150374993\ldots \approx 0.41504` bits (verified; matches Daniel's `\approx 0.415`).
- Gap = `0.0089609540\ldots \approx 0.00896` bits, **positive**.
- **Robustness check 1 (sharper Frankl):** `H_{\max}(\varepsilon)` decreases as `\varepsilon` increases (canonical concentration `\ge 1/2 + \varepsilon`). Sharper Frankl → larger deficit. Helps.
- **Robustness check 2 (weaker Frankl):** for `\Pr[\sigma_1] < 1/2`, max entropy jumps to `\log_2 6` (constraint becomes non-binding at uniform). Deficit collapses to zero. **1/2 is a sharp cliff edge; program is brittle to any weakening below 1/2.**
- **Robustness check 3 (sharper ERZ):** smaller `\Delta_{\mathrm{ERZ}}` → larger gap. Helps.
- **Robustness check 4 (weaker ERZ):** larger `\Delta_{\mathrm{ERZ}}` → smaller gap. Allowance of `\ge 0.424` already kills the program; `\ge 0.43` opens negative gap.
- **Structural interpretation of `\Delta_{\mathrm{ERZ}}`:** three possible readings — (SR-i) local-ERZ per-antichain bound (what program requires); (SR-ii) global-ERZ averaged bound (doesn't suffice); (SR-iii) tautological arithmetic (empty bound). Program requires (SR-i).

**F32.1 verdict: GREEN-arithmetic, with two robustness concerns binding on later lemmas (L2/L3 must deliver exactly `\ge 1/2`, not asymptotic; L4 must deliver local form (SR-i), not global (SR-ii)).**

#### F32.2 — Phase B: L1 (Acyclicity) is GREEN, essentially proved inline

The proof of L1 fits in 8 lines via a pair-orientation sum bound:

- Cycle `a \ll b \ll c \ll a` forces `\Pr[a<b] + \Pr[b<c] + \Pr[c<a] > 2`.
- Per-`L` enumeration: the sum is `\le 2` for every linear extension (case table over 6 relative orders of `\{a, b, c\}`, max contribution 2 per row, achieved on cyclic orders `abc, bca, cab`).
- Expectation `\le 2`. Contradiction.

**Generalisation observation.** Same argument gives `\ll` acyclic on `k`-antichains for all `k \ge 3` (with strict bias `> 2/3`).

**F32.2 verdict: L1 GREEN. No separate sub-ticket needed; inline in F32 execution doc. Budget: 50k tokens to formalise.**

#### F32.3 — Phase B: L2 (Union-Closure) AMBER

Natural-candidate failure: `Q_3 = Q_1 \vee Q_2 = \mathrm{TC}(Q_1 \cup Q_2)` creates extra canonical triples not in `S(Q_1) \cup S(Q_2)`. Concrete: `Q_1` has `a<b`, `Q_2` has `b<c`, transitive closure adds `a<c`, putting the canonical triple `\{a,b,c\}` (with order `a \ll b \ll c`) into `S(Q_1 \vee Q_2)` but not into `S(Q_1) \cup S(Q_2)`.

Per-candidate assessment:

- **L2-A (no extras in minimal counterexample):** likely false; counterexample mechanism robust to minimality.
- **L2-B (`\ll`-consistent restriction):** viable iff L1+ (transitivity of `\ll` on `\mathcal{P}(P)`) holds — a non-trivial auxiliary lemma. If L1+ holds, bridge program may simplify dramatically (unique global canonical refinement).
- **L2-C (representation lemma):** cleanest standalone candidate; requires explicit construction proving `\forall S_1, S_2 \in F(P), \exists Q_3 \ge P : S(Q_3) = S_1 \cup S_2`. Realisability question; medium tractability.
- **L2-D (upward closure):** requires combining with L3-B (weighted UCC). Cleanly formal but inherits L3 obstructions.

**F32.3 verdict: L2 AMBER. Best path L2-C (~400-600k tokens). Alternative L2-B + L1+. Multi-session.**

#### F32.4 — Phase B: L3 (Measure Transfer) AMBER with structural 1/8-obstruction

- **L3-A (direct transfer):** DEAD. Concrete counterexample: `|F(P)| = 2`, one with `A^*` and one without, gives uniform-over-`F(P)` frequency 1/2, but linear-extension frequency can be `\ll 1/2` because the two `Q`'s have wildly different `e(Q)` counts.
- **L3-B (weighted UCC):** structurally obstructed by a **1/8-factor in the natural transfer**. With weight `w(Q) = e(Q)`:
  - `\sum_Q e(Q) = \sum_L |\{Q : P \le Q \le L\}| = |\mathcal{L}(P)| \cdot 2^k` where `k = \binom{n}{2} - |P|`.
  - `\sum_{Q : A^* \in S(Q)} e(Q) = |\{L : \sigma_L|_{A^*} = \text{can}\}| \cdot 2^{k-3}`.
  - Ratio: `(1/8) \cdot \Pr_L[\sigma_L|_{A^*} = \text{can}]`.
  - So weighted-UCC giving ratio `\ge 1/2` would require `\Pr_L \ge 4`, vacuous.
  - **No natural alternative weighting bypasses the 1/8 factor.**
- **L3-C (injection):** open. Structurally cleanest if it works — bypasses the 1/8-obstruction. No constructive injection known.

**F32.4 verdict: L3 AMBER, high failure-risk. Cross-repo dependency on UC-side for L3-B salvage. Best path L3-C (~400-600k tokens). If L3-C walls, program walls at L3.**

#### F32.5 — Phase B: L4 (ERZ Entropy Contradiction) AMBER, local-vs-global unresolved

- **Local form (Lemma C):** every 3-antichain `A` in minimal counterexample has `H(\sigma_L|_A) > \log_2(9/2) \approx 2.170`. Non-standard.
- **Global form (Lemma C'):** averaged per-antichain entropy `\ge \log_2(9/2)`. Standard ERZ form. **Does NOT save program** (compatible with one antichain at 2.161 if others compensate).
- **Why local form is non-standard:** literature ERZ-style bounds (Kahn-Saks 1984, Brightwell-Tetali 2003, Friedman 1993) typically global. Local bounds require either (a) literature citation (unidentified) or (b) novel sub-poset reduction argument.
- **Sub-poset reduction sketch:** if some `A^*` has canonical-concentration `\ge 1/2`, construct a witness sub-counterexample `P' \subsetneq P` violating minimality. Multi-step, open, multi-session.
- **The `\log_2(4/3)` constant** is presented as known but has no identified literature source. Phase 1.1 (L4-α-lit) sub-ticket must identify or refute.

**F32.5 verdict: L4 AMBER, high failure-risk. Phase 1.1 sub-ticket (literature) → conditional Phase 2.1 sub-ticket (derivation). Phase 1.1 budget 150-250k; Phase 2.1 budget 400-800k.**

#### F32.6 — Phase C: refined attack order

- **Phase 0 (this scoping doc):** Phase A GREEN; L1 GREEN-inline. **Done.**
- **Phase 1 (concurrent):**
  - (1.1) F32-L4-α-lit (150-250k) — identify literature ERZ form delivering local bound.
  - (1.2) F32-L3-B-UC (200-300k, cross-repo on `union_closed`) — does UC13+UC14 extend to weighted UCC, and does any weighting bypass 1/8-obstruction?
  - **Pause after Phase 1** — evaluate verdicts before committing to L2 / L3-C / L4-β / etc.
- **Phase 2 (conditional on Phase 1):**
  - (2.1) F32-L4-β-derive (400-800k) — if Phase 1.1 RED.
  - (2.2) F32-L3-C-injection (400-600k) — if Phase 1.2 RED or AMBER.
- **Phase 3 (after L3/L4 status known):**
  - (3.1) F32-L2-C-rep (400-600k) — primary L2 attack.
  - (3.2) F32-L2-B + L1+ (400-600k) — fallback.
- **Phase 4:** F32-final integration (200-300k).

**Total typical-path budget:** 1.3M-2.4M tokens. **Worst-case:** 2.5M-4.2M tokens. Comparable in scale to UC10-UC14 Frankl-Holds chain.

**Beachhead:** width-3 first. General-width as separate sub-program if width-3 closes.

#### F32.7 — Phase D: failure modes ordered by likelihood

| # | Failure | Likelihood | Detection | Recovery | Impact |
|---|---|---|---|---|---|
| D.1 | L4 local form unavailable | HIGH | Phase 1.1 | None viable beyond L4-β-derive | RED |
| D.2 | L3 1/8-obstruction unresolvable | HIGH | Phase 1.2 / 2.2 | None viable | RED |
| D.3 | L2 four-candidate-wall | MEDIUM | Phase 3.1 | New `F(P)` (separate program) | RED for F32 |
| D.4 | Numerical gap evaporates | LOW (already verified Phase A; may resurface in 1.1 if ERZ constant differs) | Phase 0 / 1.1 | None | RED |
| D.5 | Width-3 only | LOW | Phase 4 | Width-3 partial result | AMBER |
| D.6 | L1+ unprovable | LOW | Phase 3.2 | None beyond D.3 | RED for L2-B path |

**Most likely program-walling: D.1 (L4) or D.2 (L3).** Both detected in Phase 1.

#### F32.8 — U1-dialect-collision check (clean dissolve)

F32 is purely combinatorial-probabilistic: Frankl-Holds applied to `F(P)`, entropy/ERZ contradiction. **No cohomology, no Čech complex, no `\Phi`, no refinement-respecting bridge.** The mg-26fc U1 obstruction (refinement-respecting `\mathcal{B}_P`) is structurally bypassed.

**F31's chain-locality wall remains valid but non-load-bearing for F32.** If F32 closes, 1/3-2/3 follows via the bridge program, mooting the F31 wall for the headline problem (though F31 remains a valid structural result in the Čech-bias cohomology dialect).

### Session 1 deliverables

- **`docs/compatibility-geometry-F32-uc-bridge-scope.md`** (new) — Phase A + Phase B + Phase C + Phase D, hard-constraint compliance, U1-dialect check, execution sub-ticket recommendations.
- **`docs/state-F32.md`** (new, this file) — session 1 entry.

### Session 1 verdict

**AMBER-one-lemma-tractability-uncertain.** Two lemmas (L3, L4) carry substantive execution risk; L3 and L4 are the binding constraints. **Phase 1 sub-tickets (L4-α-lit, L3-B-UC) recommended as next polecats, concurrent.** Pause for evaluation before L2 work.

### Mayor action items (post-session-1)

1. **File F32-L4-α-lit sub-ticket** (this repo, single-session, 150-250k tokens). **[DONE — Session 2 below, mg-50e2.]**
2. **File F32-L3-B-UC sub-ticket** (union_closed repo, single-session, 200-300k tokens, cross-repo). **[Still pending.]**
3. **Run concurrent.** Both are single-session paper-and-pencil + literature.
4. **Pause after Phase 1.** Mayor reviews verdicts:
   - GREEN-GREEN → proceed to L2-C-rep (Phase 3.1).
   - GREEN-RED → file L3-C-injection (Phase 2.2); defer L2 until L3 resolves.
   - RED-GREEN → file L4-β-derive (Phase 2.1); defer L2 until L4 resolves.
   - RED-RED → escalate to Daniel for program redirection.

---

## Session 2 — 2026-05-16 (F32-L4-α-lit / Phase 1.1 literature search, complete)

**Ticket:** mg-50e2 (F32-L4-α-lit). **Branch:** `polecat-cat-mg-50e2`. **Deliverable doc:** `docs/compatibility-geometry-F32-L4-alpha-lit.md` (new).

### Inputs read

- `docs/compatibility-geometry-F32-uc-bridge-scope.md` (mg-c9d9, AMBER-merged Session 1) — §3.4 (L4 tractability), §3.4.5 (Source-2 gap = the load-bearing question this session answers), §3.4.4 (global ERZ doesn't save), §1.2 (C1-C4 contradiction), §4.3 (Phase 1 strict-order recommendation), §5.1 (D.1 failure mode).
- `docs/state-F32.md` Session 1 entry (above).
- `~/files/union_closed_1323_proof_steps.txt` — Daniel's Step 8 ("Compare to ERZ 3-Antichain Bit Bound") + Step 9 ("Prove the Counting/Entropy Contradiction") — original framing.
- **Literature** (full survey enumerated in F32-L4-alpha-lit.md §1):
  - Chan-Pak survey (arXiv:2311.02743v2) "Linear extensions of finite posets" — §3.1 Prop 3.1 `[ERZ97]`, §3.6 (Theorem 3.16 Kahn-Kim entropy), §3.7 (Theorem 3.17 Brightwell-Tetali).
  - Aires-Kahn (arXiv:2510.26134) "Variance vs. range for linear extensions" — newest unconditional bound `\delta(P) \ge (5 - \sqrt 5)/10 \approx 0.345`.
  - Kahn-Saks 1984; Kahn-Linial 1991; Brightwell-Felsner-Trotter 1995; Kahn-Kim 1995; Brightwell-Tetali 2003; Sidorenko 1991; Sha-Kleitman 1986; Cardinal-et-al. 2013; Chan-Pak-Panova 2022.
  - Moitra "On entropy and extensions of posets"; Olson 2017 survey (arXiv:1706.04985).

### Findings, ordered

#### F32.S2.1 — ERZ source IDENTIFIED: Ewacha-Rival-Zaguia 1997 (closes F32-scope §3.4.5 Source-2 gap)

- **Citation.** Ewacha, Rival, Zaguia (1997), "Approximating the number of linear extensions", *TCS* 175(2), pp. 271-282. Cited as `[ERZ97]` in Chan-Pak survey Proposition 3.1.
- **Statement.** `2^k (3/4)^{\ell + m} \le e(P) \le 2^k`, where `k = ` # incomparable pairs (`A_2`), `\ell = ` # induced `A_3` (3-antichain) subposets, `m = ` # induced `(C_2 + C_1)` subposets.
- **Entropy form.** `k - (\ell + m) \log_2(4/3) \le \log_2 e(P) \le k`.
- **The constant `\log_2(4/3)`** is the per-(`A_3` + `C_2+C_1`)-substructure penalty in the ERZ lower bound. **Resolves F32-scope §3.4.5's "no specific cited source" gap** — F32-scope was tentatively pessimistic; the source exists and is well-cited.

#### F32.S2.2 — Constant `\log_2(4/3)` is SHARP in the global ERZ form

- Tight at `e(A_3) = 6 = 2^3 (3/4)^1` (`k = 3, \ell = 1, m = 0`).
- Tight at `e(C_2 + C_1) = 3 = 2^2 (3/4)^1` (`k = 2, \ell = 0, m = 1`).
- Sharpness proof: any `c < \log_2(4/3)` is refuted by `\log_2 6 \ge 3 - c \Rightarrow c \ge \log_2(8/6) = \log_2(4/3)`.
- No alternative literature ERZ-style result gives a tighter per-substructure penalty.

#### F32.S2.3 — Form mismatch: ERZ97 is GLOBAL, F32 needs LOCAL

- ERZ97: bound on `\log_2 e(P)` (total joint entropy).
- F32 Lemma C: per-individual-`A` lower bound on `H(\sigma_L|_A)`.
- Marginalisation of ERZ97 to a single `A` (§5.2 of deliverable doc) gives `H(\sigma_L|_A) \ge 3 - (\ell + m) \log_2(4/3)`, which is **vacuous** for `\ell + m \ge 8` (i.e., any non-trivial poset). For `P = A_3` itself the bound is tight at `\log_2 6` (trivial).
- This confirms F32-scope §3.4.4: global ERZ does not save the program.

#### F32.S2.4 — Scope error: F32 Lemma C local form is FALSE as written

- F32-scope §1.2 (C4) / §3.4 Lemma C says: "every 3-antichain `A` in a minimal counterexample has `H(\sigma_L|_A) > \log_2(9/2) \approx 2.170`".
- **Counterexample** (deliverable doc §3.3-§3.4): consider a minimal counterexample `P` containing a 3-antichain `\{a, b, c\}` with `\Pr_L[a < b] = 0.9` (allowed: minimal counterexample requires `\Pr \notin [1/3, 2/3]`, and 0.9 satisfies this). Other pairs `\{a, c\}, \{b, c\}` can also be strongly biased. The induced distribution on the 6 orderings has one ordering at probability `\sim 0.9` and entropy `\approx 0.7` bits, **far below** `\log_2(9/2)`.
- The local form requires hypothesis strengthening (e.g., "no pair in any 3-antichain is `\Pr > 0.9`") or quantifier weakening (e.g., "some `A` has `H \ge \log_2(9/2)`").
- **This is a substantive scope error in F32 that the polecat surfaces.** F32-scope §3.4 acknowledged "non-standard" / "possibly circular" but did not articulate this concrete refutation.

#### F32.S2.5 — Phase A gap UNCHANGED

- `\Delta_{\mathrm{can}} = \log_2 6 - [1 + \tfrac{1}{2}\log_2 5] = 0.42400` bits ✓
- `\Delta_{\mathrm{ERZ}} = \log_2(4/3) = 0.41504` bits ✓ (now literature-sourced from ERZ97)
- Gap = `0.00896` bits, positive ✓
- No Phase A redo triggered (constant matches F32-scope assumption).

#### F32.S2.6 — Verdict registration

**AMBER-no-literature-local-form-derive-needed.**

- Citation found at right constant (ERZ97).
- Constant sharp in global form.
- Form is global, not per-`A` local as F32 needs.
- Local form as F32-scope wrote it is literally false (counterexample F32.S2.4).
- Phase A gap unchanged.
- Follow-on recovery: F32-L4-corrected-scope (re-scope Lemma C, 100-200k single-session) → then F32-L4-β-derive (Phase 2.1, 400-800k multi-session) targeting the corrected lemma.

Why AMBER and not RED:
1. ERZ97 IS the literature source (F32-scope §3.4.5 gap resolved).
2. Constant is correct and sharp.
3. Phase A gap intact.
4. Recovery path exists with structural inspiration (ERZ97 per-substructure penalty mechanism).

Why not GREEN:
1. Literature form is global, not local.
2. F32 Lemma C as written is false; reformulation required before derivation can proceed.

### Session 2 deliverables

- **`docs/compatibility-geometry-F32-L4-alpha-lit.md`** (new) — full literature survey, ERZ97 identification + sharpness, gap-analysis local-vs-global, scope-error refutation of Lemma C as written, L4-β-derive prospects, follow-on recommendations.
- **`docs/state-F32.md`** (this entry) — Session 2 ledger.

### Session 2 verdict

**AMBER-no-literature-local-form-derive-needed.** L4 path forward is reformulate-then-derive, not literature-close.

### Mayor action items (post-session-2)

1. **File F32-L4-corrected-scope** (single-session, 100-200k tokens) — re-scope Lemma C in light of Session 2 F32.S2.4 counterexample. **Must precede L4-β-derive.**
2. **F32-L3-B-UC** (Phase 1.2, union_closed repo, 200-300k) — still pending; should be filed concurrently with the L4-corrected-scope as both inform the next phase.
3. **Continue to defer L2 sub-tickets** per F32-scope §4.3. L4 reformulation status governs L2 unblocking.
4. **Re-evaluate F32 verdict trajectory:** Session 1 AMBER → Session 2 AMBER-L4-needs-scope-correction. The Lemma C scope error suggests the F32 program may require more than minor adjustment — re-scoping should confirm whether the bridge program is salvageable on width-3 or whether a fundamentally different `F(P)` is needed.
5. **No Daniel escalation at this point** — the program is degraded but not walled. Daniel-articulated 10-step program may need a Step-9 rewrite (Lemma C reformulation), but Steps 1-8 + Step 10 remain intact pending L2/L3.

---

## Session 4 — 2026-05-16 (F32-width3 specialisation feasibility, complete)

**Ticket:** mg-1861 (F32-width3). **Branch:** `polecat-cat-mg-1861`. **Deliverable doc:** `docs/compatibility-geometry-F32-width3-feasibility.md` (new).
**Note on numbering:** Session 3 corresponds to the cross-repo F32-L3-B-UC sub-ticket on `union_closed` (mg-7550), which is referenced by mg-1861's body as AMBER-merged. This Session 4 entry covers the width-3 specialisation per Daniel 14:33Z directive ("try F32 in width 3 specifically").

### Inputs read

- `docs/compatibility-geometry-F32-uc-bridge-scope.md` (mg-c9d9, AMBER-merged) — §3.2 (L2 four-candidate analysis), §3.3 (L3 1/8-obstruction derivation, especially (3.3.2.4)–(3.3.2.6)), §3.4 (L4 local-vs-global), §4.4 (width-3 beachhead recommendation).
- `docs/compatibility-geometry-F32-L4-alpha-lit.md` (mg-50e2, AMBER-merged) — §1.11 (Aires-Kahn 2025 width-bounded asymptotic), §1.12 (ERZ97 source), §3.3–§3.6 (0.9-bias counterexample to general Lemma C).
- `docs/state-F32.md` Sessions 1+2 (above).
- `~/files/union_closed_1323_proof_steps.txt` (Daniel 2026-05-16T11:29Z) — original 10-step program; Steps 1–10.
- Width-3 specific literature lookups: Aires-Kahn 2025 (arXiv:2510.26134) Theorem 1.6; Linial 1984 (width-2 + N-free); Brightwell 1989 (semiorders); Brightwell-Felsner-Trotter 1995; Olson 2017 survey (arXiv:1706.04985); Stanley *Enumerative Combinatorics II*.

### Findings, ordered

#### F32.S4.1 — Phase 1 (L4 in width-3): AMBER-partial

The L4-α-lit 0.9-bias counterexample to general Lemma C is *partially* dissolved by width-3 via Aires-Kahn 2025 asymptotic (`δ(P) → 1/2` as `π(P) → ∞` for fixed width). Quantitative: for width-3, `π(P) < 36 C_3^2` is needed for `δ < 1/3` (i.e., for a minimal counterexample to exist). So width-3 minimal counterexamples (if they exist) are *small posets* (bounded `n ≈ 10`).

For small-π regime, the 0.9-bias construction is plausibly realisable (mechanism (M-2): add elements `y_i < b, y_i || a, c` to bias `\{a, b\}`; each `y_i` creates auxiliary 3-antichains `\{a, c, y_i\}` requiring minimality). The compounding constraint structure is tight but not obviously refutable.

The F32 program's own machinery for L4 (sub-poset reduction, F32-scope §3.4.3) has the *same difficulty* in width-3 as in general width. Removing an element from a width-3 minimal counterexample either decreases width to 2 (Linial closes, doesn't contradict minimality) or preserves width 3 (sub-poset's biases not controlled).

**F32.S4.1 verdict: AMBER-partial. Width-3 helps the L4 question only via external input (Aires-Kahn); F32-internal mechanism unchanged.**

#### F32.S4.2 — Phase 2 (L3 1/8-obstruction in width-3): RED-no-dissolution

The 1/8 obstruction comes from `M(L) := |\{Q : P \le Q \le L\}|` over-counting via the naive `2^k` estimate. The actual count is `\le 2^k`, reduced by transitivity constraints.

For width-3 with `\ell` 3-antichains: heuristic `M(L) \approx 2^k \cdot (7/8)^\ell` (per-triangle transitive-subset correction: 7 transitive subsets out of `2^3 = 8`). Ratio `M_A(L) / M(L) \approx 1/7` (not `1/8`).

**Empirically verified on `P = A_3`:** 19 distinct partial-order extensions; `\Sigma e(Q) = 42`; for canonical `L = abc`, `\Sigma_{Q : A \in S(Q)} e(Q) = 1`; ratio `1/42 = (1/7) \cdot (1/6) = (1/7) \cdot \Pr_L[L = abc]`. Confirms 1/7 factor.

But `1/7 < 1` is still vacuous: weighted-UCC `\ge 1/2` translates to `\Pr_L \ge 7`, infeasible.

**The structural barrier is intrinsic to `F(P)` indexing by `Q` (not `L`) and the consequent over-counting of `Q`'s per `L`.** Width-3 affects only the per-triangle correction factor (`7/8`), not this underlying structure. No natural width-3-specific alternative weighting bypasses.

**F32.S4.2 verdict: RED-no-dissolution. The 1/8 obstruction is structurally width-independent. Width-3 sharpens marginally to 1/7 but does NOT dissolve.**

#### F32.S4.3 — Phase 3 (L2 in width-3): AMBER-no-clean-simplification

`|U|` (3-antichain count) in width-3 is `O(n^3)`, same asymptotic order as general width (one element from each of 3 chains in Dilworth decomposition). Width-3 does NOT reduce `|U|` structurally.

Per-candidate:

- **L2-A (no extras in minimal counterexample):** natural-candidate failure mechanism (`Q_1` has `a<b`, `Q_2` has `b<c`, TC gives `a<c`) uses no width-3-specific structure. Still likely false.
- **L2-B (`\ll`-consistent restriction):** requires L1+ (transitivity of `\ll` across antichains). Plausibly true via probabilistic-transitivity argument à la Kahn-Saks 1984, but the argument generalises to any width — no width-3-specific shortcut.
- **L2-C (representation lemma):** transitive-closure overflow risk (TC creating extra canonical triples) unchanged in width-3. Canonical edges of `T \subseteq U` create new comparabilities the same way as in general width.
- **L2-D (upward closure + L3-B):** blocked by Phase 2 (L3-B RED in width-3).

**F32.S4.3 verdict: AMBER-no-clean-simplification. Width-3 does NOT structurally simplify L2.**

#### F32.S4.4 — Phase 4: combined verdict + Daniel recommendation

**AMBER-mixed-Phase2-RED-binding.** Phase 2 (RED) is structurally binding. Phase 1 (AMBER, partial dissolution via external Aires-Kahn input) and Phase 3 (AMBER, no simplification) do not compensate.

**Daniel's "obvious reasons" for width-3 demandingness (O.1, O.2, O.3 in deliverable §4.3) are all TRUE structural features** (every 3-antichain is a maximum antichain; canonical orientation more determined via Dilworth lattice; linear extensions bounded combinatorially). **But the F32 obstructions are orthogonal to these features.** The L3 obstruction is about `Q ↔ L` counting (not antichain rigidity); L4 is about per-antichain entropy (not maximality); L2 is about realisability of `F(P)` (not `|U|` size).

**Recommendation:** **Close F32 per Daniel's "on hold unless we learn more or have a new idea" directive (2026-05-16T14:33Z).** No execution sub-tickets (L4-width3, L3-width3, L2-width3) recommended; they would inherit Phase 2's structural RED.

Optional alternative for Daniel: file a separate scoping ticket (F33?) for "width-3 1/3-2/3 via Aires-Kahn 2025 direct + small-π exhaustive enumeration" — independent of F32 bridge program. Different program, scope separately.

### Session 4 deliverables

- **`docs/compatibility-geometry-F32-width3-feasibility.md`** (new) — Phase 1 (L4 width-3 dissolution check) + Phase 2 (L3 1/8 dissolution check) + Phase 3 (L2 simplification check) + Phase 4 (combined verdict) + hard-constraint compliance + references.
- **`docs/state-F32.md`** (this Session 4 entry) — cumulative ledger.

### Session 4 verdict

**AMBER-mixed-Phase2-RED-binding.** Width-3 specialisation does NOT provide the structural traction Daniel hypothesised. F32 should close per "on hold" directive.

### Mayor action items (post-session-4)

1. **Surface this verdict to Daniel** via mail (`mg mail send human` from the polecat). Daniel's call on whether to (a) close F32 as recommended, (b) file F33 (Aires-Kahn-direct width-3 route), or (c) pursue some other reformulation.
2. **No execution sub-tickets to file.** F32-L4-corrected-scope (Session 2's recommendation) is also moot — even with corrected Lemma C, Phase 2 L3 1/8-obstruction stands.
3. **Archive F32-series docs** (F32-scope, F32-L4-α-lit, F32-width3-feasibility) as the structural record of the attempt.
4. **F31 RED (chain-locality wall, mg-01ce) re-becomes the active milestone-1 part (iii) status** — F32 was the candidate bypass; with F32 closing, milestone-1 part (iii) reverts to F31's RED + Daniel's methodology-paper-close / milestone-1-redefinition options (per F30/F31 doc references).
5. **No Daniel-escalation-as-emergency** — the program degraded gracefully through Sessions 1 → 2 → 4, each surfacing a load-bearing concern that the next session addressed and that ultimately walled. The 10-step Daniel program remains a coherent outline; closure is recommendation, not crisis.

---
