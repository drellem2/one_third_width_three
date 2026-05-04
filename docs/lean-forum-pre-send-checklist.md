# Lean-forum publication post — pre-send checklist

This is the practical pre-send checklist Daniel should walk
through *immediately before* posting to the chosen venue. The
analogue is the outreach pre-send protocol used for direct
emails: every item below is meant to be re-confirmed at send
time, not assumed-still-true from prep time.

The companion docs are:
* [`lean-forum-post-template.md`](lean-forum-post-template.md)
  — paste-able post body.
* [`lean-forum-publication-readiness.md`](lean-forum-publication-readiness.md)
  — full claim-shape companion the post links to.
* [`lean-forum-post-venue-selection.md`](lean-forum-post-venue-selection.md)
  — venue tradeoff analysis.

## 1. Repository state

### 1.1 HEAD verification

- [ ] **Confirm `origin/main` HEAD on the public mirror.** Run
      `git -C <local mirror> ls-remote origin main` and capture
      the SHA. Confirm it matches the commit you intend to cite
      in the post body.
- [ ] **Embed the SHA in the post body.** The post template
      currently does not embed a SHA explicitly; for the send,
      add a sentence in the "Build and verify" paragraph along
      the lines of "*The post body refers to commit `XXXXXXX`
      on `main`*". This pins reviewer expectations to a specific
      tree state.
- [ ] **Confirm the public mirror is up to date with origin
      `main`.** If the GitHub repo at
      `github.com/drellem2/one_third_width_three` is behind a
      private working copy, push first.

### 1.2 `lake build` green at HEAD

- [ ] **Fresh build from a clean clone.** From a *clean* checkout
      (not the working tree polecats are running in), run:
      ```sh
      git clone https://github.com/drellem2/one_third_width_three.git /tmp/lean-fresh
      cd /tmp/lean-fresh/lean
      lake exe cache get
      lake build OneThird
      ```
      Expected: clean exit, ~3 minutes wall after `lake exe cache get`.
- [ ] **No `error` lines in the build output.** Linter warnings
      are fine; errors are not.
- [ ] **Lean toolchain version matches `lean-toolchain`.** Verify
      `lean --version` reports `4.29.1`.

### 1.3 `#print axioms` baseline matches expectation

- [ ] **Run the audit script.** From `lean/`:
      ```sh
      lake env lean scripts/PrintAxiomsAudit.lean
      ```
- [ ] **Confirm headline depends on exactly the expected axiom set:**
      ```
      [propext, Classical.choice, Quot.sound,
       OneThird.LinearExt.brightwell_sharp_centred]
      ```
      No additional project axioms; no `sorryAx`.
- [ ] **Confirm `lean/PRINT_AXIOMS_OUTPUT.txt` matches the live
      run.** If it has drifted, update it as part of a separate
      pre-send commit before the send.

### 1.4 Zero `sorry` / zero `admit`

- [ ] **Grep the lean tree.** From repo root:
      ```sh
      git grep -nE '\bsorry\b|\badmit\b' -- lean/
      ```
      Expected: any matches are confined to comments, docstrings,
      or test scaffolding clearly excluded from the production
      tree per the formalization-completeness audit
      (`docs/formalization-completeness-audit.md`). No production
      `sorry` / `admit`.
- [ ] **Cross-check with the formalization-completeness audit
      doc.** `docs/formalization-completeness-audit.md` enumerates
      where any allowed `sorry` lives (if any). If the audit doc
      asserts "0 sorries" and the grep finds production `sorry`,
      escalate before sending.

## 2. Public-mirror surface

### 2.1 README accuracy

- [ ] **Re-read the "Please read this before citing" section
      end-to-end.** Confirm:
    - Author/affiliation language matches the post template.
    - AI-assistance disclosure language matches the post
      template.
    - Lean-residuals paragraph reflects the *current* `hC3` /
      Brightwell-axiom state and the 2026-05-04 Track 1 / Track 2
      closures.
    - Known-in-tree-issue paragraph (mg-27c2 `Case2FKGSubClaim`)
      is current.
- [ ] **Verify all README-internal links resolve.** The README
      links to `docs/lean-forum-publication-readiness.md`,
      `docs/path-c-cleanup-roadmap.md`,
      `docs/path-c-track-1-status-1.md`,
      `docs/math-simp-arc-2.0/scoping.md`,
      `docs/a8-path-b-block-and-report-status.md`,
      `docs/a8-s2-restate-block-and-report-status.md`, and
      `lean/AXIOMS.md`. Each of those links should resolve to a
      file present in the tree at HEAD. Fix or drop dead links
      *before* sending.

### 2.2 Companion docs

- [ ] **Re-read `lean-forum-publication-readiness.md` end-to-end.**
      Daniel-personal review pass. Look for:
    - Stale dates (anything older than the most recent landed
      Track-1/Track-2 commits should be cited as historical, not
      current).
    - Internal contradictions (e.g., §2 saying compound-automorphism
      "would close" the gap while §5 / §7a / §9 say it has been
      shown structurally blocked — those references must agree).
    - Forward references that link to docs that no longer
      describe the current state.
- [ ] **Re-read `lean-forum-post-template.md` end-to-end.** Same
      checks as above, plus:
    - Paragraph 2 ("What the Lean side proves and what it does
      not") reflects the structural cardinality obstruction
      framing, not the older "infrastructure does not exist"
      framing.
    - Disclosure paragraph matches the README's Lean-residuals
      paragraph in substance.

### 2.3 Issue tracker labels and templates

- [ ] **Verify GitHub issues are open** on the repo (sometimes
      issues are accidentally disabled on mirror repositories).
- [ ] **Confirm at least one labelled issue category** exists for
      each kind of feedback the post invites:
    - `lean-formalization` for Lean-side critique.
    - `paper-math` for paper-level mathematical critique.
    - `disclosure` for any disclosure-honesty feedback.
- [ ] If labels do not exist, create them before sending; the
      post invites readers to file issues, and unlabeled issues
      get lost.

## 3. Adjacent-channel coordination

### 3.1 Hopkins outreach (`mg-b8f9`) status

- [ ] **Check `mg show mg-b8f9` to see whether the Hopkins email
      has been sent.** If it has been sent within the last
      ~3 days, consider delaying the forum post by 3 days.
      Rationale: the Hopkins email is a personal-collaboration
      ask; landing the forum post first risks Hopkins reading
      the public announcement before the personal email,
      flattening the personal framing.
- [ ] If the Hopkins email is **not yet sent**, no timing
      constraint from this side; consider whether the forum post
      should *precede* the personal email (different signal:
      "here's the public claim, here's why I'm asking you
      personally for review") versus *follow* it. PM judgement
      call.

### 3.2 Other outreach in flight

- [ ] **Check `outreach/collaboration_log.md`** (if maintained)
      or the most recent PM digest for any other outreach in
      flight (#3 Colin Defant or others). Apply the same
      "personal email lands before public post" preference for
      anyone whose personal email has been recently sent or is
      imminent.

## 4. Post body — final check

### 4.1 Venue-specific reframing

- [ ] **If posting to `#mathlib4` Zulip:** the template body
      pastes near-verbatim. Light edits to greeting / signoff
      conventional for Zulip threads.
- [ ] **If posting to MathOverflow:** the template body needs
      substantive reframing per
      [`lean-forum-post-venue-selection.md`](lean-forum-post-venue-selection.md)
      §3.4: lead with the math claim, mention the formalization
      as supporting evidence, drop the "Lean-side eyes" framing.
      This is a *different post*, not a copy-paste.
- [ ] **If posting to mailing list:** more formal opening; the
      post body is otherwise compatible with the template.

### 4.2 Disclosures

- [ ] **AI-assistance disclosure** is present in the post body
      verbatim from the template, not softened or moved to a
      footnote.
- [ ] **No-external-review-yet disclosure** is present.
- [ ] **Author-affiliation disclosure** is present.
- [ ] **Stop-loss for hostile readers** is present ("*if you
      consider AI-assisted mathematics a categorical
      disqualifier you should stop here*"). This is a stated
      `feedback_audit_as_deliverable` line; do not omit.

### 4.3 Links

- [ ] **Every link in the post body resolves.** Spot-check at
      least:
    - Repository URL.
    - `MainTheorem.lean` direct link (with line numbers if any).
    - `lean-forum-publication-readiness.md` URL.
    - `path-c-cleanup-roadmap.md` URL.
    - `lean/AXIOMS.md` URL.
    - `PRINT_AXIOMS_OUTPUT.txt` URL.
    - `step8.tex` references via `main.pdf`.
- [ ] **No links to private branches / draft files / WIP.**

## 5. Post-send (within 24h)

These are not pre-send items but should be planned at send time.

- [ ] **Bookmark the thread URL** for follow-up.
- [ ] **Subscribe to the thread** if the venue supports it
      (Zulip stream subscription, MO question follow,
      mailing-list reply-all).
- [ ] **Set a check-in cadence** — e.g., 24 hours, 72 hours,
      1 week — for monitoring response. Most engagement on
      `#mathlib4` Zulip arrives within the first 48 hours.
- [ ] **Plan response-handling triage.** Lean-side critique →
      file as GitHub issue and reply with link. Paper-side
      critique → reply in-thread; if substantive, file an
      issue. Disclosure-tone feedback → reply in-thread, no
      issue needed.

## 6. Stop-and-escalate triggers

- **Build fails on the fresh clone (item 1.2).** Do not send.
  Escalate (mail to mayor / file ticket) and resolve before
  sending.
- **`#print axioms` reports an unexpected axiom (item 1.3).**
  Do not send. Escalate.
- **`sorry` / `admit` found in production tree (item 1.4).**
  Do not send. Escalate.
- **README links broken (item 2.1).** Fix before sending.
  Send-time pause is fine; sending with broken links is not.
- **Internal contradiction in companion docs (item 2.2).** Do
  not send. Reconcile docs first.
- **Outreach timing conflict surfaced (item 3.1).** Pause and
  reassess; not necessarily a stop, but a "discuss with PM
  before sending" signal.

## 7. Audit-bar disclosure check

`feedback_audit_as_deliverable` and `feedback_signature_regressions`
both apply at send time. Specifically:

- The post body **must not** soften or hide the `hC3` hypothesis.
  The template's paragraph 2 leads with `hC3` in bold and
  spends a substantial paragraph on it; do not edit this down
  on the venue-specific paste.
- The post body **must not** soften the Brightwell-axiom
  disclosure. The retain-rather-than-port decision is part of
  the deliverable's honesty surface.
- The post body **must not** characterise the math-simp arc
  closures as "in progress" or "next steps"; both arcs closed
  RED-fallback. The template currently characterises them
  correctly; a quick edit to soften the language would violate
  `feedback_distinguish_arc_chunk_outcomes`.

## 8. References

* Forum post template: [`lean-forum-post-template.md`](lean-forum-post-template.md).
* Companion readiness doc:
  [`lean-forum-publication-readiness.md`](lean-forum-publication-readiness.md).
* Venue selection: [`lean-forum-post-venue-selection.md`](lean-forum-post-venue-selection.md).
* Track 1 status: [`path-c-track-1-status-1.md`](path-c-track-1-status-1.md).
* Track 2 status: `docs/math-simp-arc-2.0/scoping.md`
  (branch `math-simp-arc-2.0`, commit `b1ac92b`).
* Path C parked-work audit:
  [`path-c-cleanup-roadmap.md`](path-c-cleanup-roadmap.md) §7
  (revival triggers).
* Filed under `mg-721a` ("Lean-forum publication post — prep +
  venue selection") by polecat `p721a` on 2026-05-04.
