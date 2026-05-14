# F10 general-n unified-proof cumulative state (mg-8216)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs deferred across the
multi-session (300k cap) F10 ticket.

**Branch:** `compat-geom-F10-general-n-proof` (mg-8216).
**Goal (mg-8216):** synthesize the two GREEN general-n mechanisms —
M1 (mg-6295 PCR-Lit-2 cofiber Morse) + M2 (mg-759d PCR-Lit-3 FI
rep-stability) — with the ICOP framework (mg-1e99) into a unified
general-n proof skeleton for width-3 Kahn–Saks 1/3-2/3. NO new
axioms; no Lean changes; no new HPC; no new empirical n-datapoint
(per `feedback_focus_on_induction_not_special_cases`). The closure
must be structural (cofiber-Morse + FI rep-stability), NOT empirical
pattern extrapolation — mg-14a0 proved the direct Plan-H route does
not generalize.

**Outcome (after Session 1):** **GREEN-conditional.** The §6 proof
skeleton completes — width-3 1/3-2/3 at general n is reduced, with no
logical gap, to a single master hypothesis (UCC). M1 + M2 provably
combine: they converge on (UCC). See the Session-1 ledger below and
`docs/general-n-proof-synthesis.md`.

---

## Session ledger

### Session 1 — 2026-05-14 (this polecat, mg-8216) — DONE

**Goal:** Read the three parent mechanisms (M1/M2/ICOP), verify the
mandatory trip-wires, draft the comprehensive proof-synthesis document,
identify the load-bearing open gap, emit a verdict.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read parents: mg-6295 (M1), mg-759d (M2), mg-1e99 (ICOP), mg-7b3b/mg-3bf3 (n=6), mg-b345 (Quillen-fiber), mg-f91f/mg-59f3 (n=4 cofiber), mg-14a0 (Plan-H non-generalization) | ✅ | — |
| Trip-wire (a): mg-6295 GREEN reproduces (0,0,2,0) cofiber Betti at n=3→4 | ✅ PASS | synthesis §1.5 |
| Trip-wire (b): mg-759d GREEN — sgn-twist constant at n=3,4,5,6 | ✅ PASS (with §7.2 refinement) | synthesis §1.5 |
| Trip-wire (c): mg-1e99 §6 ICOP matches general-n template | ✅ PASS | synthesis §1.5 |
| Comprehensive proof document `docs/general-n-proof-synthesis.md` (§1–§11) | ✅ | the deliverable |
| §6.2 inductive step — gap-free cofiber-LES diagram chase | ✅ | Hyp(n) ⇒ Hyp(n+1) given (UCC) |
| §6.3 master conditional hypothesis (UCC) isolated | ✅ | Uniform Cofiber Concentration + injectivity |
| §6.4 M1 + M2 shown to combine (converge on UCC) | ✅ | RED-mechanism-gap excluded |
| §7.2 conditional-hypothesis verification — sharpened to (FG-Cofiber) | ✅ | corrects mg-759d diagonal-FI framing |
| §10 n=7 cross-validation (paper-and-pencil, no new HPC) | ✅ | M1/M2 predictions mutually consistent at n=4..7 |
| §8 Lean-port roadmap (high level) | ✅ | L0–L3 staged; recommend no port pre-(UCC) |
| §9 methodology-paper-grade summary | ✅ | conditional theorem + single open-gap statement |
| Verdict | ✅ **GREEN-conditional** | see below |

**Verdict: GREEN-conditional.**

The §6 proof skeleton **completes**: width-3 Kahn–Saks 1/3-2/3 at
general n is reduced, with no logical gap, to the single master
conditional hypothesis **(UCC)** — Uniform Cofiber Concentration:
for all n, H̃*(Δ_{n+1}/Δ_n) is concentrated in degree n−1, equals
2·sgn_{S_n}, and the connecting map δ_n is injective.

Key structural findings:

1. **The cofiber long exact sequence is the actual synthesis bridge.**
   Given Hyp(n) [= H-Cox + sgn at level n] and (UCC) at level n, the
   cofiber LES of the pair (Δ_{n+1}, Δ_n) gives Hyp(n+1) by a
   gap-free diagram chase (§6.2). Base case Hyp(3) rigorous. So
   (UCC) ⇒ Hyp(n) for all n.

2. **M1 and M2 converge on (UCC).** M1 (cofiber Morse) supplies the
   acyclic matching n-uniformly; (UCC) is exactly "M_rel is perfect."
   M2 (FI rep-stability) supplies the base data + template; (UCC) is
   exactly "the cofiber-cohomology FI-object is finitely generated of
   presentation degree 0." Two independent machineries, same crux.
   Both PROVE (UCC) at n=3→4. RED-mechanism-gap decisively excluded.

3. **The gap is sharpened beyond mg-759d's framing.** mg-759d's
   "sgn-twisted diagonal = M(0), presentation degree 0" is NOT a
   theorem about the geometric co-FI-module: the geometric diagonal
   does not carry a naive co-FI-module structure at all, because the
   cohomological degree (n−2) shifts with n while pullback ι*
   preserves degree (§7.2.a). The correct stable object is
   degree-shift-aware — the cofiber-cohomology sequence with the
   connecting-map transition maps, or the F8'' Quillen fiber X_n.
   The precise open statement is **(FG-Cofiber)** (§7.2.c).

4. **The CEF/Patzt-Putman criterion does not apply off-the-shelf**
   (§7.2.d): the natural finite ambient (relative cochain complex)
   is itself not finitely generated (mg-759d §7). Three viable
   specialist routes enumerated; none closed (Tier-3, consistent
   with finish-internally directive — attack stays internal, residual
   honestly recorded).

5. **Secondary conditional inputs, both narrowed.** (ICOP-step) §5.4:
   the per-step BFT-sharp bound reduces to one structurally-uniform
   lex-min cover step per n (the inherited steps are n-independent by
   the F8' multiplicativity law). Width-3 bridge §7.3: rigorous m≤4,
   conditional m≥5, reduces to (ICOP-step) + "ι-tower meets every
   width-3 orbit." Neither is "beyond FI finite generation" in kind;
   both verified n≤6.

**Trust surface impact:** NONE. No new axioms; no Lean changes; no new
computation. Pure structural cohomology + paper-and-pencil. The in-tree
Lean `width3_one_third_two_thirds` 4-axiom trust surface is untouched.

**Deliverables produced this session:**
- `docs/general-n-proof-synthesis.md` (NEW) — §1–§11, the comprehensive
  proof-synthesis document.
- `docs/state-F10.md` (NEW, this file) — cumulative state ledger.

**Nothing deferred to a Session 2.** The F10 ticket's deliverables
1–5 are all addressed in Session 1:
- D1 comprehensive proof document — ✅ `general-n-proof-synthesis.md`.
- D2 conditional-hypothesis verification — ✅ §7.2 (a/b/c/d): the
  sharpened (FG-Cofiber) statement, why CEF/Patzt-Putman is not
  off-the-shelf, the three specialist routes.
- D3 n=7 cross-validation (paper-and-pencil) — ✅ §10.
- D4 load-bearing OPEN gap identified — ✅ (UCC) / (FG-Cofiber), §6.3 + §7.2.
- D5 trust-surface impact — ✅ none, §1.4.

If the mayor / a follow-up wants more, the natural Session-2 / follow-on
tickets are (all Tier-3, all out of F10 scope):
- **(FG-Cofiber) closure** — set up the degree-shift-aware functor
  category and prove finite generation. The deep item.
- **PCR-Lit-2′** — verify M1's M_rel is perfect at n=4→5 (mg-6295's
  own designated follow-up; would verify (UCC.1) at one more n).
- **F8'' continuation** — explicit Quillen fiber X_n identification.

---

## Invariants (reproduce-on-resume)

For any future session, these are the load-bearing facts; re-derive /
re-check against the parent docs before extending:

- |PPF_3|=12, |PPF_4|=194, |PPF_5|=4110, |PPF_6|=129302.
- H̃^k(Δ_n) = sgn_{S_n} if k=n−2 else 0, at n=3,4,5,6 (n=6 has one
  extrapolated Euler-char term — synthesis §4.4 note).
- Cofiber Δ_4/Δ_3: H̃* = (0,0,2,0) = 2·sgn_{S_3}, δ_3 injective
  (mg-6295, mg-f91f, mg-59f3). This is (UCC) at n=3, PROVEN.
- M_{n+1} = M_n ⊔ M_rel acyclic for ALL n (downward-closed-subcomplex
  lemma, n-independent — mg-6295 §6.1).
- F8' multiplicativity: |L(ι_{n-1}(P_k))| = n·|L(P_k)| — inherited
  per-step Pr ratios are n-independent.
- 16/16 per-step BFT-sharp on canonical critical chains at n=3,4,5,6.
- (UCC) §6.3 is THE load-bearing gap; (FG-Cofiber) §7.2.c is its
  sharpened precise form.
- mg-14a0: direct empirical Plan-H route PROVABLY does not generalize
  — do NOT close via pattern extrapolation; closure must be structural.
