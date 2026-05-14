# F12 methodology-paper-draft cumulative state (mg-59d0)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs deferred across the
multi-session (400k cap) F12 ticket.

**Branch:** `compat-geom-F12-methodology-paper` (target); polecat branch
`polecat-cat-mg-59d0`.
**Goal (mg-59d0):** draft the methodology paper. Spine = F10 §9 (the
complete, gap-free reduction of width-3 Kahn–Saks 1/3-2/3 to the single
representation-stability hypothesis (FG-Cofiber), with M1+M2 shown to
converge on it). LaTeX-first; NO new axioms; no Lean changes; no new
computation. Pure write-up + synthesis from in-tree F-series docs.

**Repoint note:** mg-59d0 was filed as F9-S3 (a verdict-dependent stub).
Repointed by pm-onethird 2026-05-14: F10 (mg-8216, GREEN-conditional)
superseded the F9 framing entirely, so the paper's spine is the F10
general-n synthesis. Dependency mg-14a0 removed; budget 100k→400k;
unshelved.

**Outcome (after Session 1):** **AMBER-partial-draft.** All 11 sections
of `docs/methodology-paper-draft.tex` are substantive and the LaTeX
compiles clean (17 pp, 0 errors, 0 undefined refs). The draft is
ready for Daniel review. A handful of refinements are flagged for an
optional Session 2 — none load-bearing; see the ledger below and
`docs/methodology-paper-status.md`.

---

## Session ledger

### Session 1 — 2026-05-14 (this polecat, mg-59d0) — DONE

**Goal:** Pull the F-series source docs, draft the full 11-section
LaTeX methodology paper per the mg-59d0 section plan, write the
cumulative state + status docs, verify the LaTeX compiles, submit.

**Sources pulled (read, not re-derived):**

| Source | Branch | Used for |
|--------|--------|----------|
| `docs/general-n-proof-synthesis.md` (F10, mg-8216) | `compat-geom-F10-general-n-proof` | **Spine** — §1–§11 of the paper map onto F10 §1–§11; §9 of F10 is the abstract/exec summary |
| `docs/state-F10.md` (F10) | `compat-geom-F10-general-n-proof` | invariants cross-check |
| `docs/state-F9.md` (F9, mg-9e88/mg-14a0) | `compat-geom-F9-S2-n7-pattern` | §9 documented obstruction (Plan-H) |
| `docs/compatibility-geometry-F9-constructive-lift.md` (F9 S1) | `compat-geom-F9-S2-n7-pattern` | §9 — Plan-H mechanism, n=5/6 closure |
| `docs/compatibility-geometry-F9-session-2.md` (F9 S2) | `compat-geom-F9-S2-n7-pattern` | §9 — n=7 super-polynomial obstruction, Findings A/B |

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read F10 master synthesis (the spine) | ✅ | — |
| Read F9 Sessions 1+2 (documented obstruction) | ✅ | — |
| Read state-F10 / state-F9 (invariants) | ✅ | — |
| `docs/methodology-paper-draft.tex` — §1 Introduction | ✅ | substantive |
| §2 Background + trust surface | ✅ | substantive; trust-surface independence from the Lean artifact stated explicitly |
| §3 Statement of the conditional theorem | ✅ | Thm 3.1 (preview) + Thm 7.5 (final form, §7.7) |
| §4 Mechanism M1 — cofiber discrete Morse | ✅ | downward-closed-subcomplex lemma + n-uniform/n-dependent split |
| §5 Mechanism M2 — FI rep-stability | ✅ | incl. §4.4 n=6 honesty note; cofiber LES as the bridge |
| §6 ICOP framework + n-uniform reduction | ✅ | ι-tower, (ICOP-step) |
| §7 The proof — M1+M2+ICOP combined | ✅ | §7.2 gap-free diagram chase; (UCC) Hyp 7.1 in §7.3; §7.4 convergence; §7.5 base case; §7.6 width-3; §7.7 final theorem (Thm 7.5) |
| §8 The single open gap — (FG-Cofiber) | ✅ | §7.2.a–d sharpening; CEF/Patzt-Putman not off-the-shelf; 3 routes |
| §9 Documented obstruction — Plan-H | ✅ | n=5,6 closure; n=7 super-polynomial; Findings A/B; lesson for the framework |
| §10 Empirical anchor — n=3,4,5,6 | ✅ | m_sgn=1; (UCC) proven n=3→4; 16/16 ICOP; n=6 Euler-term honesty note |
| §11 References | ✅ | 12-item literature list (F10 §11.2) |
| Appendix A — Lean formalisation roadmap | ✅ | L0–L3 staged; recommend no port pre-(UCC) |
| LaTeX compiles | ✅ | `pdflatex` ×2, 17 pp, 0 errors, 0 undefined refs, 69 labels resolved |
| `docs/state-F12.md` | ✅ | this file |
| `docs/methodology-paper-status.md` | ✅ | per-section status + venue thoughts |
| Verdict | ✅ **AMBER-partial-draft** | see below |

**Verdict: AMBER-partial-draft.**

All 11 sections are substantive — this is not a skeleton. The reason
the verdict is AMBER and not GREEN-draft-complete is that a methodology
paper of this kind benefits from a second editorial pass that this
polecat is deliberately leaving for a follow-up session (or for
Daniel's review to direct):

- **No figures.** The paper would be strengthened by (i) a Hasse-style
  picture of the cofiber pair Δ_n ⊂ Δ_{n+1}, (ii) the cofiber LES
  diagram, (iii) a "two-mechanisms-one-crux" schematic. Currently all
  prose + tables.
- **§9 obstruction could cite the explicit ψ-coefficient/anomaly table**
  from F9 Session 2 §0.2 verbatim — currently summarised.
- **Width-3 reduction (step 1 of the skeleton)** is stated at the level
  F8 left it; if a reader wants the F4 five-obstruction-map lineage
  spelled out, that is a possible §7.3 expansion.
- **Front matter** (author block, acknowledgements, MSC codes) is
  placeholder — "Compat-Geom working group".
- The draft has **not** been read end-to-end by a mathematician for
  exposition flow; that is what Daniel review is for.

None of these are load-bearing: the mathematics is the F10 synthesis
verbatim-faithful, and the LaTeX is clean. AMBER here means
"spine complete, ready for review, polish deferred" — exactly the
multi-session-continuation case the ticket's AMBER tag describes.

**Trust surface impact:** NONE. No new axioms; no Lean changes; no new
computation. The in-tree Lean `width3_one_third_two_thirds` 4-axiom
trust surface is untouched and is explicitly noted in §2.4 / Appendix A
as an independent track.

**Deliverables produced this session:**
- `docs/methodology-paper-draft.tex` (NEW) — full 11-section LaTeX
  article + Appendix A, compiles clean.
- `docs/state-F12.md` (NEW, this file) — cumulative state ledger.
- `docs/methodology-paper-status.md` (NEW) — per-section status + venue.

---

## F11 coordination note

F12 is **independent of F11 (mg-b352)**. F11 attacks (FG-Cofiber); F12
writes up the framework. The paper is written so that an F11 closure is
a **localized revision, not a rewrite**:

- If F11 closes (FG-Cofiber): §8 (`sec:opengap`) changes from "the
  single open problem" to "the theorem of [F11]"; §7's Theorem 7.5
  (`thm:final`) parts (i)–(ii) upgrade from *conditional on (UCC)* to
  *unconditional*; the abstract and §1.3 contribution list drop the
  word "conditional" for the core. The two secondary inputs
  ((ICOP-step), width-3 bridge) are unaffected — they were never
  governed by (UCC).
- Concretely: the localized edits are the abstract, §1.3, §3 (Thm 3.1),
  §7.7 (Thm 7.5), and §8.1–§8.2. Everything else (M1, M2, ICOP, the
  diagram chase, the obstruction, the empirical anchor) stands as-is.

If F11 comes back AMBER/RED, no F12 change is needed — the paper is
already written for the conditional case.

---

## Invariants (reproduce-on-resume)

For any future session, these are the load-bearing facts; they are the
F10/F9 invariants the paper rests on. Re-check against the parent docs
before extending.

- |PPF_3|=12, |PPF_4|=194, |PPF_5|=4110, |PPF_6|=129302.
- H̃^k(Δ_n) = sgn_{S_n} if k=n−2 else 0, at n=3,4,5,6 (n=6 has one
  extrapolated Euler-char term — paper §5.5 / §10.1 honesty note).
- Cofiber Δ_4/Δ_3: H̃* = (0,0,2,0) = 2·sgn_{S_3}, δ_3 injective.
  This is (UCC) at n=3, PROVEN (paper §7.5 / §10.2).
- M_{n+1} = M_n ⊔ M_rel acyclic for ALL n (downward-closed-subcomplex
  lemma, n-independent — paper Lemma 4.1).
- F8' multiplicativity: |L(ι_{n-1}(P_k))| = n·|L(P_k)| — inherited
  per-step Pr ratios are n-independent; inherited profile
  (7/15,4/7,1/2,1/2,…).
- 16/16 per-step BFT-sharp on canonical critical chains at n=3,4,5,6.
- (UCC) is THE load-bearing gap (paper §7.3, Hyp 7.1); (FG-Cofiber)
  is its sharpened precise form (paper §8.2.c, Hyp 8.1).
- Plan-H direct route: closes inductive step at n=5,6, PROVABLY does
  not generalize (B_n = 10,64,1607; u_n = 4,54,1597,65099 —
  super-polynomial; near-diagonal structure degrades at n=7). This is
  paper §9, the documented obstruction.
- NO new axioms; LaTeX-first; closure must be structural, not
  pattern-extrapolation.

---

## Optional Session 2 scope (not load-bearing)

If the mayor / Daniel wants a Session 2 before review, or review
directs one:
1. Add the three figures listed in the verdict.
2. Expand §9 with the verbatim F9-S2 §0.2 headline table.
3. Spell out the F4 five-obstruction-map lineage in §7.3.
4. Fill front matter (authors, MSC 06A07 / 55U10 / 20C30,
   acknowledgements).
5. End-to-end exposition pass.

If F11 (mg-b352) closes (FG-Cofiber) before review, fold in the
localized revision per the F11 coordination note above.
