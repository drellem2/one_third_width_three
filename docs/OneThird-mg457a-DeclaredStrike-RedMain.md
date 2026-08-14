# mg-457a — GET MAIN GREEN: the declared strike was made, one document over

**Status:** closed. `main` was red for 5h across 4 runs; one cause; the control was right and is
unchanged. The repair is a single keyed baseline entry, and this document is the finding that the
baseline comment requires before anyone adds one.

**Verdict in one line.** `mg-cd04`'s declared-strike control caught a real pattern and did exactly
its job. The clause it caught is a **cross-document strike report that names its subject**: it
reports a retraction made in another file, and names the retracted sentence by quoting it. The
retraction is real, it is at the named destination, and it carries the `~~` markup there. So the
clause describes a strike rather than making one, and the correct remedy is to record it.

---

## 1. The failure, and that it was one cause

    FAIL: a block declares a strike and does not make it:
      OneThird-mg52c4-PerPoset-Subposet-Question.md — "restriction maps carry local-to-global content"

Workflow `Script controls`, step *mg-cd04 declared-strike control*, exit 1. Four consecutive red
runs on `main` (31755003161, 31757793162, 31758752267, 31766307631), last green `bec18a04`
2026-08-13T12:56. Those four run identifications and their per-run failing step are `pm-onethird`'s
measurement, taken at 04:05Z and reported in the mg-457a ticket; this document did not re-fetch
them from the API.

What **was** re-derived here, from the tree rather than from the run log:

- `git log -L 68,68:docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` names **cf63bb3** as the
  commit that wrote the clause — the first red run's head, and the file's own creation commit.
  Nothing since has touched that line.
- `2d4abbf` (`land mg-72e4's amendment AT ITS DESTINATION`, 03:58) does touch the same document and
  was **not** covered by any of the four runs. It neither repaired nor compounded the defect: with
  `origin/main` at `75fb81d` — which contains `2d4abbf` — the control still exits 1 at the same
  site. The newer commit was checked rather than assumed, and it changed nothing here.

## 2. The site, and why the strike is not missing

The tripping clause is item 4 of §0 of `OneThird-mg52c4-PerPoset-Subposet-Question.md`, line 68.
Reproduced verbatim, inside a fence, because reproducing it as prose in this document would
promise a strike this document does not make — the fence is the corpus's marked way to quote a
block as literal data:

```
4. **Two F28 statements are wrong and are struck at their destination** (§3.1–§3.2): (F-5)
   *"restriction maps carry local-to-global content"* is **vacuous**, and §2.3's identification
   `Δ(↑P ∖ {P}) = lk_{Δ_n}(P)` **drops the lower factor** — the very factor Theorem A computes.
```

Three words in that clause carry the whole decision: **at their destination**. The destination is
`docs/compatibility-geometry-F28-sheaf-cohomology-on-POSET.md`, and the edit landed there:

```
(F-5) **Sub-site framework.** Up-sets `\uparrow P` parametrise BK-subposet families; ~~restriction maps carry local-to-global content~~.

> **STRUCK 2026-08-14 (mg-52c4) — the second clause is vacuous.** ...
```

`git log -L 205,205:docs/compatibility-geometry-F28-sheaf-cohomology-on-POSET.md` puts that markup
in **cf63bb3** — the same commit that wrote the summary clause. The author did not forget the
markup. The author put it at the destination, said so in the summary, and named which of the two
F28 statements was meant by quoting it.

So the two remedies the control offers are not a coin flip here. Remedy (1) — *add `~~` at the
site* — is for a document that meant to retract its own text. `mg-52c4` never asserts that F28
sentence; it quotes it as a name.

## 3. Why remedy (1) is not merely unnecessary but wrong, and it was measured

Three reasons, in increasing order of how much they cost:

1. **It would misreport what is retracted.** Rendering the quotation struck inside §0 says
   `mg-52c4` retracted a clause of its own summary. Nothing in `mg-52c4` is retracted.
2. **It would contradict the same document three sections down.** §3.1 blockquotes the identical
   F28 sentence **unstruck**, deliberately, as the thing being adjudicated, and only then rules on
   it. Quoting the pre-strike text is how the adjudication is legible at all.
3. **It would silently widen this control far more than the baseline entry does.** Backing is
   tested **per block**, and the block here is lines 34–75 — 42 lines spanning §0 items 3, 4 and 5
   plus the `mg-e08a` scoping note. One `~~` at that quotation exempts *every* declaration in all
   42 lines, unnamed and unprinted. The baseline entry exempts one keyed (file, quote) pair, is
   counted in `baseline : N tolerated site(s)`, and fails the run if it ever stops matching.

That third point is the one that decides it on the control's own terms. The ticket's warning —
don't reach for the baseline because it turns the build green faster — is exactly right as a
default, and here the *other* remedy is the one that buys a bigger, quieter tolerance.

A fourth option existed and was rejected: **reword the clause** so it no longer matches the
`DECLARATION` regex (e.g. "and §3.1–§3.2 strike them at their destination"). That turns the build
green and leaves no record. The next author who writes the natural phrasing trips the control
again, with nothing on file saying why it was decided the first time. Recording is what the
baseline channel is *for*.

## 4. What the class actually is, and the one thing this leaves open

The control's docstring already excludes reports of edits made elsewhere — quoted here inside a
fence, for the reason §5 gives:

```
a block that says a claim "is struck" without quoting anything is reporting on an edit made
elsewhere, which is what most of this corpus's prose about strikes is.
```

The exclusion is carried by the words **without quoting anything**. This site is that same kind of
report — with the subject named by quotation. The rule cannot separate the two, because separating
them means deciding whether a quoted span is *this block's text* or *a name for another block's
text*, and that is a content judgement; content-free structure is the whole reason this control
generalises to the 269 documents this run classified, where the `mg-8a71` signature sweep reads 1.

So the residue is a **narrow, named, low finding, and it is left open on purpose**: a cross-document
strike report that names its subject will trip this control every time, and each one costs a
baseline entry and a paragraph. Nothing here changes what the control checks, its rule, or its
exemption channels — the ticket says not to, and after reading the site that is also the right call.

**Not measured:** how many such reports the corpus will accumulate, and therefore whether the
baseline grows linearly in them. One site over the control's lifetime is not a rate, and the
nearest neighbour — `OneThird-mg8a71-VerdictRepairs-Closeout.md:16`, the sole entry in the
never-failed-on near-miss channel — is a related but not identical shape (its declaration and its
quotation are in the same block, not the same sentence).

## 5. The remedy exhibited the defect it remedies, and the check caught it

A remedy is an artifact of the same kind as the defect, so it is subject to it. This document is
prose in `docs/`, which is precisely the population `mg-cd04` sweeps — so before committing, the
control was run **against the repair**, not only against the original site.

It failed. The first draft of §4 above quoted the control's own docstring in a **blockquote**:

```
OneThird-mg457a-DeclaredStrike-RedMain.md:96
  FAIL: a block declares a strike and does not make it — "is struck"
```

The docstring sentence contains the phrase in quotation marks, so the `DECLARATION` and
`QUOTATION` regexes both matched inside one sentence of an unmarked block — a document explaining
why a strike report is not a strike declaration, promising a strike it did not make, on the same
page. That is `mg-069f`'s original G1 shape (the defect authored one document over from the
instrument that had just closed it), reproduced a third time.

The fix is the mechanism the control already provides and its docstring already names: the
docstring quotation now sits in a **fence**, which is how this corpus reproduces a block as literal
data rather than asserting it. Both fenced reproductions in §2 were written that way from the start
for the same reason.

**And it then happened a second time, in this section.** The paragraph above originally reproduced
that FAIL line as a 4-space indented block. An indented block is not a fence — `mg-cd04` skips
```` ``` ```` and `~~~` regions only — so the reproduction of the failure re-created the failure,
one paragraph below the paragraph explaining it. Fenced, and the run then went green. Neither
recurrence was predicted; both were found by running the control on the repair before the commit
rather than after the merge, which is the only part of this that was a decision.

## 6. Files

| file | change |
|---|---|
| `scripts/onethird_mgcd04_declared_strike_control.py` | one `BASELINE` entry, keyed `(OneThird-mg52c4-PerPoset-Subposet-Question.md, "restriction maps carry local-to-global content")`, with the reasoning above in the comment above it. The rule, the regexes, the exemption channels and `--demonstrate` are untouched. |
| this document | the finding the baseline comment requires before an entry is added. |

Verified after the change: the control exits **0** with `baseline : 3 tolerated site(s)` and the
`mg-52c4` site printed as `[BASELINE]`; and `--demonstrate bb1cb9b` still exits **0**, i.e. the
control still bites at the revision where the original `mg-0242` G1 defect is live.
