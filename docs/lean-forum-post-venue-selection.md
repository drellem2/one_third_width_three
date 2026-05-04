# Lean-forum publication post — venue selection

This document compares candidate public venues for the
forum-publication post (template:
[`lean-forum-post-template.md`](lean-forum-post-template.md);
companion: [`lean-forum-publication-readiness.md`](lean-forum-publication-readiness.md))
and lays out tradeoffs along the dimensions that matter for this
particular post. **The polecat does not pre-pick the venue;
Daniel does.** The doc is here to make the comparison transparent
so the call is informed.

## 1. Candidate venues

Four primary venues are in scope, plus one not-quite-a-venue
option (the GitHub repo itself) and one combination strategy.

### 1.1 Lean Zulip — `#mathlib4` stream

**URL.** `leanprover.zulipchat.com`, stream `#mathlib4` (the
mathlib-development stream).

**Audience.** mathlib core developers, regular contributors,
formalization-focused researchers. Highly Lean-fluent; varying
combinatorics depth. Mathematicians actively engaged with the
formalization side of poset / order-theoretic content (e.g.,
the `Order/PartialOrder` and `Combinatorics/Posets` mathlib
sub-libraries) read this stream.

**Formality / register.** Casual conversational threads with
near-real-time response. Long technical posts are welcomed but
unusual.

**Response-loop dynamics.** Fast (hours to days). Discussion
tends to be Lean-mechanical ("can this be a `def` instead of a
`structure`?") rather than mathematics-mechanical. Critique
quality is high on Lean fidelity, more variable on combinatorics
depth.

**Fit for this post.**
* **Strengths.** Native venue for "I have a Lean 4 formalization
  and want eyes on the formalization" — this is what `#mathlib4`
  exists for. The repo is Lean-side, the headline gap (`hC3`) is
  Lean-side. Reader expectations align with the post's primary
  ask. Cross-references to mathlib (`Order.Cover`,
  `Order.LinearExtension`) will be parsed. Probability that
  someone reads the `Mathlib/RelationPoset/FKG.lean` audit
  carefully is highest here.
* **Weaknesses.** Less likely to surface paper-level mathematics
  critique — the kind of reader who would notice a flaw in
  Step 5/6/7's BK / fiber / coherence analysis is over-represented
  in the math research community, under-represented on
  `#mathlib4`. The post would land but the "Lean-side eyes" framing
  steers attention away from the paper-level review the project
  also wants.
* **Disclosure tone.** The Zulip community is generally welcoming
  of AI-assisted mathematics framed honestly; the README's
  "Please read this before citing" section is the right tone.
  Under-disclosure risk: low; over-disclosure risk: also low —
  the audience is professional enough to read past the
  disclosures.

### 1.2 Lean Zulip — `#general` stream

**URL.** Same as above, stream `#general`.

**Audience.** All Zulip subscribers (broader than `#mathlib4`),
including users who are Lean-curious but not mathlib core.

**Formality / register.** Same as `#mathlib4` — casual
conversational threads.

**Fit for this post.**
* **Strengths.** Slightly broader reach. Mainstream Lean
  community visibility.
* **Weaknesses.** A formalization-of-a-research-claim post is
  arguably more topical for `#mathlib4` than `#general`; some
  readers will mentally redirect, lowering engagement. Splitting
  posts across both is a known anti-pattern.
* **Verdict.** Almost certainly worse than `#mathlib4` alone for
  this post; not recommended as a primary venue.

### 1.3 proofassistants.SE forum

**URL.** `proofassistants.stackexchange.com`.

**Audience.** Cross-system formalization audience (Lean, Coq,
Isabelle, Agda). Relatively small (compared to `#mathlib4`) but
high signal-to-noise. Readers tend to be experienced
formalization practitioners.

**Formality / register.** Stack Exchange Q&A format. Posts are
typically *questions*, not announcements. The natural shape for
this content there is "Has anyone seen X technique used to
discharge a hypothesis like `Case3Witness`?" or "Is there a
Mathlib idiom for FKG-style sub-claims I should be using?" —
not a release-announcement.

**Response-loop dynamics.** Slower than Zulip (days to weeks).
Permanent, searchable record once posted.

**Fit for this post.**
* **Strengths.** Persistent record; good for surfacing
  cross-system expertise (e.g., Isabelle/HOL has its own poset
  combinatorics work and FKG infrastructure that might inform
  the in-tree formalization).
* **Weaknesses.** Format mismatch — this isn't a question, it's
  an announcement-with-disclosures. A literal SE post would feel
  forced; the audience would correctly read it as venue-
  inappropriate. Better used as a *secondary* venue with a
  reframed-as-question post if a specific cross-system question
  surfaces.
* **Verdict.** Not a primary venue. Possibly a follow-on if a
  specific Lean-side question (e.g., "How do other formalizations
  handle universally-quantified discharge hypotheses like
  `Case3Witness`?") emerges from the primary venue.

### 1.4 MathOverflow

**URL.** `mathoverflow.net`.

**Audience.** Research mathematicians (broad). Order theory /
combinatorics tag (`po.posets`, `co.combinatorics`) has active
specialists.

**Formality / register.** Research-level Q&A, very high standard
of mathematical rigor in posts and comments. Announcements per
se are rare; the natural shape is a question (e.g., "What is the
status of compound-automorphism dispatch arguments for width-3
posets?" or, if reframed, "Has anyone seen a proof of the
1/3-2/3 conjecture for width 3 outside the published partial
results?").

**Response-loop dynamics.** Slow (days to weeks); high signal
when it comes.

**Fit for this post.**
* **Strengths.** This is the highest-credibility venue for
  paper-level mathematical critique. The kind of expert who
  would notice a flaw in Step 5/6/7 (fiber / coherence /
  globalization) reads MO. If the structural argument has a
  hole, MO is where it would be found.
* **Weaknesses.** The post as currently drafted is a
  Lean-formalization announcement, not a math-research question.
  An MO post would need substantive reframing — likely:
  * Drop the Lean-formalization framing from the primary post.
  * Lead with the mathematical claim and the structural argument
    sketch.
  * Mention the formalization as supporting evidence, not as
    the focus.
* **AI-assistance disclosure tension.** MO readers are a more
  conservative audience on AI-assisted mathematics than the Lean
  Zulip community. The README's disclosure section is the
  bare-minimum-honest framing; some MO commenters will
  nonetheless write the post off categorically. That's a real
  cost (lost engagement) but not a cost worth hiding the
  AI-assistance from — which would be both wrong and futile
  given the post's other framing.
* **Verdict.** Highest-leverage venue *if* the post is reframed
  as a math-research announcement and the polecat / Daniel are
  comfortable with the AI-assistance disclosure visibility risk.
  Lower-leverage if the current Lean-side framing is kept (the
  audience mismatch goes the other way: MO readers don't deeply
  audit Lean code).

### 1.5 Lean community mailing list

**URL.** `leanprover-community.github.io` (the community page;
mailing list link from there).

**Audience.** Overlaps significantly with Zulip but skews older
and less actively interactive. Many subscribers are
read-only.

**Formality / register.** More formal than Zulip; closer to a
mailing-list announcement format.

**Response-loop dynamics.** Slow. Mailing-list discussion is
typically lower-volume and higher-formality than Zulip.

**Fit for this post.**
* **Strengths.** Reaches Lean community members who don't read
  Zulip actively. Relatively formal medium suitable for an
  announcement.
* **Weaknesses.** Mostly redundant with Zulip; people who would
  engage substantively are also on Zulip. Cross-post overhead
  without much marginal reach.
* **Verdict.** Not a primary venue. Optional cross-post if Daniel
  wants the mailing-list audience explicitly; low priority.

### 1.6 GitHub issues on the repo itself (not a venue, but the post says so)

**URL.** `github.com/drellem2/one_third_width_three/issues`.

The post template asks readers to file issues for specific
in-tree feedback. This is the *channel* for follow-up after the
post lands, not the venue for the post itself, but worth flagging
because the venue choice should be backstopped by ensuring
issues are open, the README is current, and labels exist for
the kind of feedback expected (e.g., "lean-formalization",
"paper-math", "disclosure").

## 2. Tradeoff axes

The four primary venues differ across five axes:

| Axis | `#mathlib4` (Zulip) | `#general` (Zulip) | proofassistants.SE | MathOverflow | Mailing list |
|---|---|---|---|---|---|
| **Audience fit (Lean-side)** | High | Medium | Medium-High | Low | Medium |
| **Audience fit (paper-side)** | Low-Medium | Low | Low | High | Low-Medium |
| **Response-loop speed** | Hours-days | Hours-days | Days-weeks | Days-weeks | Slow |
| **Persistence (search-discoverability)** | Medium | Medium | High | High | Low-Medium |
| **AI-assistance disclosure tolerance** | Generally accepting | Generally accepting | Mixed | Mixed-conservative | Generally accepting |
| **Format alignment with post** | Native | Adequate | Forced (Q&A only) | Forced (would need reframing) | Native |

## 3. Combination strategies

### 3.1 Single-venue: `#mathlib4` Zulip only

Simplest. Aligns with the post's "Lean-side eyes" framing.
Misses paper-side critique potential.

### 3.2 Sequential: `#mathlib4` first, then MO 1-2 weeks later

Lead with `#mathlib4` because the post is most natively framed
for that venue. After 1-2 weeks of Lean-side engagement,
optionally cross-post to MO with a substantive math-side
reframe (drop Lean-formalization as primary framing; lead with
structural argument; reference Lean tree as supporting evidence).
Reframed MO post is *not* a copy-paste of the Zulip post; it is
a different post for a different audience.

This is more work but covers both audiences without
format-mismatching either.

### 3.3 Simultaneous: `#mathlib4` Zulip + MathOverflow

Risks of simultaneous post:
* Same-author posts to two distinct venues *at the same time*
  is sometimes read as audience-shopping. Less of a concern if
  the post bodies are distinctly tailored to each venue (no
  copy-paste) and reasoned about as such.
* Comment-thread fragmentation — discussion at one venue won't
  inform discussion at the other. Manual cross-linking needed.

Generally inferior to sequential. Not recommended.

### 3.4 Single-venue: MathOverflow only

Plausible if the post is *substantively reframed* away from
"Lean formalization announcement" toward "structural proof
sketch with Lean-formalization supporting evidence". The current
template is not that post; it would need a substantial rewrite.

Requires more pre-flight work than starting at `#mathlib4`, but
could be a higher-leverage single venue if the goal is research
math critique rather than Lean-side eyes.

## 4. Recommendation tier

The recommendation here is intentionally tiered: the polecat
does not pre-pick a single venue. Daniel's call.

**Tier A (recommended primary).** **`#mathlib4` Zulip stream.**
The post as currently drafted is a near-native fit. Best
expected response-loop. Audience expectations align with the
post's framing. Lowest pre-flight overhead.

**Tier B (recommended follow-on).** **MathOverflow** with a
substantive math-side reframe of the post body, ~1-2 weeks after
the Zulip thread settles. This step is **conditional on Daniel's
preference** for paper-side critique reach — it costs more
pre-flight work (re-drafting the post for MO format and
audience) and exposes the AI-assistance disclosure to a more
conservative audience.

**Tier C (situational).** **proofassistants.SE** if a specific
cross-system question emerges from the Zulip thread, framed as
a question rather than an announcement.

**Tier D (low-priority).** **Lean community mailing list** if
Daniel wants explicit mailing-list reach. Mostly redundant with
Zulip.

**Not recommended.** **`#general` Zulip stream as primary.**
`#mathlib4` is strictly better for this content. Use only if
Daniel has a specific reason to bypass `#mathlib4` (e.g., a
prior thread there made the topic unwelcome).

## 5. Other considerations

### 5.1 Hopkins outreach (`mg-b8f9`) timing

Per the pre-send checklist
([`lean-forum-pre-send-checklist.md`](lean-forum-pre-send-checklist.md)),
the Hopkins email send should be considered. Sam Hopkins is
plausibly active on `#mathlib4` and reads MO. If the Hopkins
email has already been sent (status in `mg show mg-b8f9`),
delaying the forum post by ~3 days lets the email land in his
inbox before he sees the public-channel announcement, which
preserves the personal-collaboration-ask framing of the email.
If the email has not been sent, no timing constraint applies.

This is a soft scheduling consideration, not a hard
precondition.

### 5.2 Author affiliation in post body

Daniel has explicit instructions in the README's "Please read
this before citing" section: "*The work was undertaken by an
unaffiliated individual without a formal background in
combinatorics or order theory.*" The post template echoes this
("*The author is unaffiliated…*"). Both should be retained
verbatim regardless of venue. This is a `feedback_audit_as_deliverable`
discipline point: the disclosure is part of the deliverable's
honesty surface.

### 5.3 Posting account hygiene

If posting to MathOverflow or proofassistants.SE, the posting
account should match the GitHub identity (`drellem2`) so
readers can trace post → repo → README → disclosures without
account-linking ambiguity. This is a Daniel-side check, not a
polecat consideration; flagged here for completeness.

## 6. Conclusion

`#mathlib4` Zulip is the strongest single-venue choice for the
current draft. MathOverflow is the strongest follow-on if Daniel
wants paper-side critique reach and is willing to absorb the
re-drafting cost and the more conservative AI-assistance
disclosure audience. Other venues are situational or low-priority.

The polecat's deliverable is this comparison. Daniel picks the
venue and the timing.

## 7. References

* Forum post template: [`lean-forum-post-template.md`](lean-forum-post-template.md).
* Companion readiness doc:
  [`lean-forum-publication-readiness.md`](lean-forum-publication-readiness.md).
* Pre-send checklist:
  [`lean-forum-pre-send-checklist.md`](lean-forum-pre-send-checklist.md).
* Hopkins outreach ticket: `mg show mg-b8f9`.
* Filed under `mg-721a` ("Lean-forum publication post — prep +
  venue selection") by polecat `p721a` on 2026-05-04, in
  response to PATH A pivot after Track 1 / Track 2 closures.
