# Lean-forum publication post prep — status (mg-721a)

**Work item:** `mg-721a` ("Lean-forum publication post — prep +
venue selection (PATH A ship pivot after Track 1/2 RED)").

**Polecat:** `p721a`, 2026-05-04.

**Status:** **Done.** Four deliverables landed; no blockers
surfaced; PATH A is the settled outcome and the post is now
ready for Daniel's send (under a follow-on action ticket).

---

## TL;DR

* Track 1 (`mg-b666`) and Track 2 (`mg-80ab`) both closed RED
  on 2026-05-04. PATH A ("ship the documented narrower public
  claim under the reframed wording established in `mg-9e50` /
  `mg-457c`") is now the **settled** outcome rather than the
  default-after-park.
* Four docs landed in this commit:
    * `docs/lean-forum-post-template.md` — refreshed
      paragraph 2 ("What the Lean side proves and what it does
      not") to remove the obsolete "300–500 LoC of compound-
      automorphism infrastructure that does not exist in the tree"
      framing; replaced with the structural cardinality
      obstruction framing plus Track 2's zero-GREEN scoping
      verdict. Updated the calibration paragraph too.
    * `docs/lean-forum-publication-readiness.md` — refreshed
      Status header from 2026-04-27 to 2026-05-04 with a new
      "Update relative to the 2026-04-27 calibration" block
      summarising both Track closures; rewrote §2 to reflect the
      structural obstruction (compound-automorphism kit DID land,
      mg-84f2 / mg-c0c7 / mg-02c2, but cannot extend to
      case-2-strict by cardinality); rewrote §5's
      "Future-revival pathways" to reflect that math-simp arc
      2.0 ran and RED'd; rewrote §7a similarly; added a §9
      provenance entry.
    * `docs/lean-forum-post-venue-selection.md` — new doc.
      Compares `#mathlib4` Zulip / `#general` Zulip /
      proofassistants.SE / MathOverflow / Lean community
      mailing list across five tradeoff axes. Recommends a
      tiered approach (`#mathlib4` Tier A primary; MO Tier B
      conditional follow-on; SE Tier C situational; mailing
      list Tier D low-priority) but does not pre-pick.
      Daniel's call.
    * `docs/lean-forum-pre-send-checklist.md` — new doc. 8
      sections: repository state (HEAD, build, axioms, sorry/admit
      grep), public-mirror surface (README accuracy, companion
      docs, issue tracker labels), adjacent-channel coordination
      (Hopkins outreach `mg-b8f9` timing), post body final check
      (venue reframing, disclosures, link verification),
      post-send (next 24h), stop-and-escalate triggers,
      audit-bar disclosure check.
* `README.md` — audited; "Please read this before citing"
  Lean-residuals paragraph and Known-in-tree-issue paragraph
  updated to reflect Track 1 / Track 2 closures and to remove
  the obsolete "infrastructure does not exist" framing.

* No new axioms, no `sorry` / `admit`, no Lean code changes.
  `#print axioms width3_one_third_two_thirds` baseline unchanged.
* PM next call: file the follow-on action ticket for Daniel's
  send (this polecat does not post; per brief, Daniel sends on
  his own timing).

---

## 1. What the brief asked for and what was delivered

The brief (`mg show mg-721a`) listed four deliverables; all four
landed:

| Deliverable | File | Status |
|---|---|---|
| Refreshed forum-post template | `docs/lean-forum-post-template.md` | Updated |
| Refreshed publication-readiness doc | `docs/lean-forum-publication-readiness.md` | Updated |
| New venue-selection doc | `docs/lean-forum-post-venue-selection.md` | Created |
| New pre-send checklist | `docs/lean-forum-pre-send-checklist.md` | Created |

Plus a fifth implicit ask: audit the README's "Please read this
before citing" section for consistency. That landed too —
`README.md` "Please read this before citing" updated.

## 2. What changed since the 2026-04-27 calibration

Two material findings since 2026-04-27 that the PATH A docs were
not yet calibrated against:

### 2.1 Track 1 RED (`mg-b666`, 2026-05-04, commit `5dff5e4`)

Per `docs/path-c-track-1-status-1.md`, the natural in-tree
dispatch route — extending the K=2 same-band compound-
automorphism kit (mg-84f2 / mg-c0c7 / mg-02c2, in tree) to also
discharge case-2-strict — is structurally impossible.

The argument is one paragraph (`docs/path-c-track-1-status-1.md`
§2a): any order-preserving permutation `σ : α ≃ α` with
`σ a = a'` restricts to a bijection `upper(a) → upper(a')`,
forcing `|upper(a)| = |upper(a')|`, contradicting the strict
inclusion that defines case-2-strict.

The obstruction holds for triple-orbit, partial-injection, and
different-pair variants of compound-automorphism (§3 of that
doc). It is independent of Lean encoding (§2d). It rules out the
compound-automorphism path *for any construction*, not just the
ones tried.

The complementary probability-bound route was already known
blocked at K=2 (mg-b0de's Brightwell-vacuous-at-`|Q| ≤ 6`
finding); §4 of the Track 1 doc rehearses why.

### 2.2 Track 2 RED (`mg-80ab`, 2026-05-04, commit `b1ac92b` on
branch `math-simp-arc-2.0`)

Per `docs/math-simp-arc-2.0/scoping.md`, a fresh-framing scoping
pass surveyed four candidate alternate framings:

| Framing | Verdict |
|---|---|
| 1: Audit-bar revisit (multi-element Brightwell axiom) | RED — fails 2/4 audit-bar conditions (external + low-risk) |
| 2a/2b/2c: Direct probability bound bypassing FKG | RED — disposed of by mg-a79e / mg-b0de or paper-level math discovery |
| 3: Restrict-and-dispatch | RED standalone; AMBER as Track 1 fallback only |
| 4: Different proof program (Brightwell-pump / Kahn-Saks / Linial alternate) | RED — out of polecat scope |

**Zero GREEN framings.** Verdict: *"No good framing found this
round; Track 1 remains the path."* But Track 1 also closed RED
hours earlier on the same day.

### 2.3 What the two closures imply for PATH A

Before 2026-05-04, PATH A was the *default* outcome under
pm-onethird's option (δ): retain `hC3`, ship the audit, revisit
if a Path C revival trigger fires later. The implicit assumption
was that compound-automorphism was effort-bound (300–500 LoC of
work that hadn't been done) and that math-simplification was a
viable parallel arc.

After 2026-05-04, PATH A is the **settled** outcome. The
compound-automorphism path is now structurally closed (cardinality
obstruction), and the math-simplification arc has been scoped
twice (2026-05-02 arc 1.0; 2026-05-04 arc 2.0) without finding a
GREEN framing. The remaining revival routes — A8-S2-cont
(2000–3500 LoC infrastructure), width-3 Kahn–Linial tightening
(paper-level math discovery), or a fresh proof program — are all
multi-week or external-collaboration scope, none of them
"one-polecat work".

The forum-post template's paragraph 2 was the principal carrier of
the obsolete framing. It is now replaced.

## 3. Doc-by-doc summary

### 3.1 `docs/lean-forum-post-template.md`

* **Calibration paragraph (top of doc).** Updated to cite both
  Track closures explicitly; states that PATH A is now "settled"
  rather than "default".
* **Paragraph 2 of the post body ("What the Lean side proves
  and what it does not").** Rewritten. Old wording said
  `hC3` closure "*requires roughly 300–500 LoC of compound-
  automorphism infrastructure that does not exist in the tree*"
  and that "*the parked decision is firm pending either a
  mathlib-side compound-automorphism primitive or a focused
  multi-week pass*". Both clauses are now wrong: the
  infrastructure DID land (mg-84f2 / mg-c0c7 / mg-02c2), and
  even with it, the cardinality obstruction blocks the
  case-2-strict dispatch. The new wording lays out both Track
  closures explicitly (named-citing the audit docs), then lists
  the three remaining revival routes (A8-S2-cont; width-3
  Kahn–Linial tightening; different proof program).
* **Other paragraphs (axioms, known in-tree issue, build, status
  disclosures).** Unchanged in substance; no drift detected.

### 3.2 `docs/lean-forum-publication-readiness.md`

* **Status header (§ 1, top of doc).** Date updated 2026-04-27 →
  2026-05-04. New "Update relative to the 2026-04-27 calibration"
  block summarises both Track closures and explicitly states
  PATH A is the settled outcome.
* **§ 2 ("What `hC3 : Case3Witness` is and why it is parked").**
  Rewritten. Acknowledges the compound-automorphism kit landed
  (mg-84f2 / mg-c0c7 / mg-02c2) and quotes the Track 1 cardinality
  obstruction. Removes the now-misleading "300–500 LoC of
  compound-automorphism math … that does not exist in the tree
  today". Ends with an explicit list of the three remaining
  revival routes.
* **§ 5 ("Known in-tree issue: mg-27c2 `Case2FKGSubClaim`")
  Future-revival pathways block.** Rewritten. The two original
  pathways (A8-S2-cont; math-simplification experiment) are now
  more narrowly scoped: math-simp arc 1.0 and 2.0 both ran and
  closed without GREEN framings; references both. Adds a third
  pathway that arc 2.0 raised (finite-enumeration certificate B2
  for K=2 case-2-strict) flagged AMBER as a Track 1 fallback only
  per arc 2.0's recommendation.
* **§ 7a ("The `hC3` Prop-level hypothesis").** Rewritten. Old
  wording was effort-bound ("300–500 LoC … that does not exist
  in the tree"); new wording is structurally settled (cites
  Track 1 cardinality obstruction). Section header subtitle
  "(open math, parked)" → "(open math, settled park)".
* **§ 9 ("Provenance").** New paragraph appended documenting the
  mg-721a refresh, listing the Track 1 and Track 2 commits as
  the fresh evidence.

### 3.3 `docs/lean-forum-post-venue-selection.md` (new)

8 sections covering five candidate venues + a not-quite-a-venue
option (GitHub issues for follow-up) + combination strategies.
Comparison table on five axes (audience fit Lean-side, audience
fit paper-side, response-loop speed, persistence, AI-disclosure
tolerance, format alignment). Tiered recommendation: `#mathlib4`
Tier A primary; MathOverflow Tier B conditional follow-on (with
substantive math-side reframe required); proofassistants.SE
Tier C situational; mailing list Tier D low-priority. Polecat
does not pre-pick; Daniel does.

### 3.4 `docs/lean-forum-pre-send-checklist.md` (new)

8 sections of practical checklist items: repository state (HEAD
verification, `lake build` green, `#print axioms` matches,
sorry/admit grep), public-mirror surface (README accuracy,
companion docs, issue tracker labels), adjacent-channel
coordination (Hopkins outreach `mg-b8f9` timing — soft
preference for ~3 day delay if Hopkins email recently sent),
post body final check (venue reframing if MO, disclosures
verbatim, links resolve), post-send 24h plan, stop-and-escalate
triggers (build fails / unexpected axiom / sorry in tree / broken
links / internal contradiction → STOP), audit-bar disclosure
check (do not soften `hC3`, Brightwell axiom retain decision, or
math-simp closure framing under `feedback_audit_as_deliverable` /
`feedback_signature_regressions` / `feedback_distinguish_arc_chunk_outcomes`).

### 3.5 `README.md` ("Please read this before citing")

* **Lean-residuals paragraph.** Rewritten to reflect Track 1
  cardinality obstruction and Track 2 zero-GREEN scoping verdict.
  Adds explicit links to the Track 1 status doc and the Track 2
  scoping doc.
* **Known-in-tree-issue paragraph.** "Future-revival routes" list
  trimmed: math-simplification experiment is downgraded from a
  parallel option to a "was attempted, closed without GREEN
  framings" reference. The remaining in-scope revival route is
  A8-S2-cont; everything else is research-arc / external.

## 4. Audit-bar discipline

Per the brief:
* `feedback_audit_bar_for_axioms` holds. **No new axioms
  proposed** in any of the docs.
* `feedback_signature_regressions` holds. **No softening of the
  `hC3` hypothesis.** The post template's paragraph 2 still
  leads with `hC3` in bold and dedicates a substantial paragraph
  to it; the disclosure surface is preserved verbatim.
* `feedback_distinguish_arc_chunk_outcomes` holds. **The doc
  refresh leads with substantive outcome, not B1's parallel
  cleanup**: the language "Track 1 RED, Track 2 RED, PATH A
  settled" is the plain-talk framing; nowhere do the docs
  attempt to lean on B1's ship to imply progress on `hC3`.

## 5. Blockers surfaced (none substantive)

The brief listed three stop-loss / block-and-report triggers.
None fired:

* **Substantive paper-vs-Lean mismatch surfaced by the refresh?**
  No. The refresh re-derived the same `hC3` / Brightwell axiom
  surface as the 2026-04-27 calibration; the only material
  change is *why* the park is now structurally settled. The
  side-by-side reading in §1 of the readiness doc is unchanged.
* **Build break at HEAD?** Not checked end-to-end (this is a
  docs-only ticket; build verification is itself the *deliverable*
  pre-send checklist's responsibility). The Track 1 status doc
  (commit `5dff5e4`) reports "no Lean code changes; #print axioms
  unchanged"; subsequent commits on main since then are the
  pm-onethird roadmap regenerations and this commit, neither of
  which touches Lean code. Build expected green.
* **Audit-bar reconsideration?** No. The Brightwell axiom
  disclosure language is unchanged and remains the canonical
  "external published bound transcribed under retain-rather-than-
  port" framing.

## 6. What this polecat does NOT do

* **Does not post.** Per the brief, the post is sent under a
  follow-on Daniel-assigned action ticket on Daniel's own timing.
* **Does not pick the venue.** The venue-selection doc is a
  comparison + tiered recommendation; Daniel picks.
* **Does not edit the LaTeX or the Lean code.** Docs-only.
* **Does not change `lean/AXIOMS.md`** (the Brightwell axiom
  documentation is current; no change required).
* **Does not change `lean/PRINT_AXIOMS_OUTPUT.txt`** (the baseline
  is current; the build was not re-run for this docs-only
  commit).

## 7. PM next-action items

1. **File the follow-on action ticket** (Daniel-assigned, not
   polecat) for the actual send, citing this prep ticket and
   the four landed docs.
2. **Coordinate with `mg-b8f9` (Hopkins outreach) timing.** Per
   the pre-send checklist §3.1, if Hopkins email lands first,
   delay forum post by ~3 days. PM judgement call.
3. **Track that the `lake build` / `#print axioms` checks in
   pre-send checklist §1.2 / §1.3 are run** *before* Daniel's
   send, not skipped.

## 8. References

### Primary (this round)

* `docs/lean-forum-post-template.md` — refreshed forum-post
  template.
* `docs/lean-forum-publication-readiness.md` — refreshed
  publication-readiness doc.
* `docs/lean-forum-post-venue-selection.md` — new venue-selection
  doc.
* `docs/lean-forum-pre-send-checklist.md` — new pre-send
  checklist.
* `README.md` — refreshed "Please read this before citing"
  Lean-residuals paragraph.

### Inputs

* `docs/path-c-track-1-status-1.md` (commit `5dff5e4`,
  `mg-b666`) — Track 1 cardinality-obstruction
  block-and-report.
* `docs/math-simp-arc-2.0/scoping.md` (commit `b1ac92b` on
  branch `math-simp-arc-2.0`, `mg-80ab`) — Track 2 fresh-framing
  scoping verdict.
* `docs/lean-forum-publication-readiness.md` (pre-refresh, last
  edited 2026-04-27 under `mg-457c`) — prior calibration.
* `docs/lean-forum-post-template.md` (pre-refresh, last
  calibrated to `mg-457c` / option (δ) park) — prior template.
* `docs/path-c-cleanup-roadmap.md` §7 — revival triggers.
* `docs/a8-path-b-block-and-report-status.md` (`mg-a79e`) —
  `Case2FKGSubClaim` direction-wrong finding.
* `docs/a8-s2-restate-block-and-report-status.md` (`mg-b0de`) —
  η₄ block-and-report on `≤ 2/3` upper bound.
* `mg show mg-b8f9` — Hopkins outreach #2 ticket.
* `project_publication_readiness.md` — PATH A is the no-OVERRIDE
  outcome.

### Discipline anchors

* `feedback_audit_bar_for_axioms` — no new axioms.
* `feedback_signature_regressions` — `hC3` hypothesis disclosure
  preserved verbatim.
* `feedback_distinguish_arc_chunk_outcomes` — outcome framing
  leads with substantive verdict, not B1 parallel ship.
* `feedback_audit_as_deliverable` — disclosure surface is part of
  the deliverable; pre-send checklist §7 enforces.
* `feedback_block_and_report` — applied to the Track 1 / Track 2
  inputs (both block-and-reports).
* `feedback_latex_first_for_math_simp` — applied via the Track 2
  `docs/math-simp-arc-2.0/scoping.md` upstream.

### Reminders / origin

* Daniel directive (in-session, 2026-05-04T18:34Z), via `mg show
  mg-721a` "Origin" section: *"Drive next slice now: review the
  Track 1 status doc + Track 2 scoping doc and either (a) file
  follow-on Track 2 execution tickets if scoping found a viable
  framing, or (b) re-park Path C per option (B) and pivot. Do
  not wait for sweep."*

## 9. Final state

* **Branch:** `polecat-p721a` (this worktree).
* **Token cost:** ~70k orient + read inputs; ~30k drafting; total
  well under the 300k ticket budget.
* **No code changes; no axiom changes; no build invocation.**
* **`#print axioms width3_one_third_two_thirds`** baseline
  unchanged from `5dff5e4`.
* **PM next-call:** file the follow-on action ticket for
  Daniel's send (this polecat does not post).
* **Polecat done after refinery merge confirms.**
