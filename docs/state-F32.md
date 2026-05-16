# State F32 — Union-Closed → 1/3-2/3 bridge program (mg-c9d9) — cumulative state

**Ticket:** mg-c9d9 (F32-scope, scoping session). **Branch:** `polecat-cat-mg-c9d9`. **Parent:** Daniel reminder 2026-05-16T11:29:58Z articulating a 10-step proof program at `~/files/union_closed_1323_proof_steps.txt` to bridge from union-closed (Frankl-Holds via UC10+UC12+UC11+UC13+UC14 chain, all merged 2026-05-16) to 1/3-2/3 via canonical 3-antichain families. Cross-repo: the program *invokes* Frankl-Holds (which lives on `union_closed` repo) but lives on the 1/3-2/3 side (this repo, `one_third_width_three`).
**Type:** Multi-session F-series arc. Session 1 = scoping; execution sessions to follow if scoping GREEN/AMBER.
**Status:** scoping session 1 in progress (this document).
**Verdict (after session 1):** **AMBER-one-lemma-tractability-uncertain** — Phase A numerical-constants verify (gap `\approx 0.00896` bits, real); L1 (acyclicity) essentially proved in scoping; L2/L3/L4 carry execution risk with L3 and L4 binding. Recommended next action: file two Phase 1 sub-tickets (L4-α-lit, L3-B-UC) as concurrent polecats; pause for evaluation.

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

1. **File F32-L4-α-lit sub-ticket** (this repo, single-session, 150-250k tokens).
2. **File F32-L3-B-UC sub-ticket** (union_closed repo, single-session, 200-300k tokens, cross-repo).
3. **Run concurrent.** Both are single-session paper-and-pencil + literature.
4. **Pause after Phase 1.** Mayor reviews verdicts:
   - GREEN-GREEN → proceed to L2-C-rep (Phase 3.1).
   - GREEN-RED → file L3-C-injection (Phase 2.2); defer L2 until L3 resolves.
   - RED-GREEN → file L4-β-derive (Phase 2.1); defer L2 until L4 resolves.
   - RED-RED → escalate to Daniel for program redirection.

---
