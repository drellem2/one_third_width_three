#!/usr/bin/env python3
"""mg-8a71 — a *doc-level* control for the mg-fccb §2.3 direction repair.

WHY THIS EXISTS, AND WHY THE NUMERIC CONTROL IS NOT ENOUGH.
`scripts/onethird_mgfccb_direction_check.py` proves `b_x <= m_x` on a corpus of
posets.  It cannot see the defect it was written for.  The defect was never a
false *number*: it was a false *sentence sitting in live body text*, and mg-fccb's
own stated reason for striking it rather than annotating it was that mg-1fdb's
annotation "left the wrong claim in the body".  That is a property of the
document, so it needs a document-level check.

WHAT IT CHECKS.  In `docs/OneThird-L1b-Spread-Locality.md`, the refuted inference

    a large per-element inversion DEGREE  max_x m_x  falsifies lemma (B)
    (equivalently: (B) "hinges on" capping m_x; equivalently: the bimodal
     chain-cross question and the max_x m_x question are the same question)

must not be asserted in **live body text**.  Text inside a *marked* blockquote --
one whose opening lines carry `~~` (struck), `ANNOTATION`, `STRUCK`, or
`RE-DERIVATION` -- is not live: that is the corpus's convention for retaining a
refuted claim as a record.  An unmarked blockquote (a display) IS live.  So is a
plain paragraph -- except for any `~~inline strikethrough~~` span inside it,
which is the same convention applied at sentence granularity and is stripped
before the signatures are applied (added mg-069f, when the §5 fix below needed to
strike one sentence of a numbered-list item without striking the item).

HOW FAR A MARKER REACHES (mg-cd04, closing mg-0242 finding G2).  mg-069f stopped
a STRIKE block exempting itself by its label alone -- such a block is now checked
with inline `~~` spans removed, so declaring STRUCK without the markup fails.
That tightening was applied to ONE of the two marker classes.  EXEMPT blocks
(`ANNOTATION` / `RE-DERIVATION`) were still skipped ENTIRELY on a label read from
`block[:3]`, with NO bound on how long the block ran; mg-0242 demonstrated the
gap by mutation (refuted sentence in an ANNOTATION tail -> exit 0, MISSED; the
same sentence as a paragraph -> exit 1, caught) and showed it was not
hypothetical -- the longest ANNOTATION block in this file runs 53 lines and
swallows load-bearing prose that mg-069f itself wrote.

An EXEMPT marker now reaches only as far as the thing it is a marker FOR:

  * the block is split into sub-paragraphs at its own blank (`>`-only) lines;
  * the sub-paragraph carrying the label is exempt, for at most MAX_LABEL_LINES
    lines;
  * each following sub-paragraph is exempt only while it carries a QUOTATION --
    a `~~struck~~` span or a quoted sentence.  Commentary about a refuted claim
    has to quote the claim, and that quotation is the whole reason the exemption
    exists; a sub-paragraph that quotes nothing is not commentary, it is body
    text, and the exempt run ENDS there;
  * a quotation-backed sub-paragraph is exempt for at most MAX_QUOTED_LINES
    lines (mg-9d7b);
  * and in no case does one block's labels and quotations exempt more than
    MAX_EXEMPT_LINES lines of text between them (mg-9d7b).

Everything past the exempt prefix is checked as an ordinary quote unit.  This is
the same rule as the strike tightening -- BACK THE LABEL WITH MARKUP -- applied
to the class it was missing, plus the length bound the strike form gets for free
by being per-sentence.

THE SECOND CHANNEL, AND WHY THE DOCSTRING ABOVE USED TO BE FICTION (mg-9d7b,
closing mg-9a19 finding H1).  Between mg-cd04 and mg-9d7b the two paragraphs
above named `MAX_EXEMPT_LINES` twice and NO SUCH IDENTIFIER EXISTED.  The only
constant was `MAX_LABEL_LINES`, and it bounded the label's own sub-paragraph.
So the bound a reader was promised was block-level and the bound the code had
was sub-paragraph-level, and a reader taking the docstring at its word concluded
that appending body text to a quotation-backed sub-paragraph was impossible.  It
was not: mg-9a19's M4 did exactly that and exited 0.  mg-cd04 bounded ONE of the
two ways a line can leave this control on a marker's say-so and left the other
exempt entire, at any length -- 66 lines over 9 sub-paragraphs at that tree,
against 59 it had just moved out of the blind spot.  Both are bounded now, the
identifier exists, and the docstring is a description rather than a promise.

EVERY CHANNEL, AND WHAT EACH ONE COSTS.  This control is a filter, so the useful
question is not "what does it check" but "by what routes does text leave it".
There are eight, and `--channels` prints the reach of all of them on every run:

    A1  the EXEMPT label sub-paragraph        BOUNDED MAX_LABEL_LINES
    A2  a quotation-backed sub-paragraph      BOUNDED MAX_QUOTED_LINES  <- H1
    A3  one block's exempt total              BOUNDED MAX_EXEMPT_LINES
    A4  a blockquote's own blank `>` lines    not text; counted
    A5  inline ~~struck~~ spans               UNBOUNDED BY DESIGN, reach printed
    A6  the population: one document          UNBOUNDED BY SCOPE, argued, printed
    A7  fenced code                           NOT a channel here -- fences are
                                              CHECKED (see the asymmetry note)
    A8  label detected in block[:3] but the
        exemption granted to sub-paragraph 0  mismatches reported

A5 is the one nobody had named.  `INLINE_STRIKE.sub(" ", text)` deletes text from
EVERY checked unit -- paragraph, heading and STRIKE block alike -- before a
signature ever sees it, at any length, and until mg-9d7b no run printed a number
for it.  It stays unbounded, and that is a decision rather than an oversight:
inline `~~` IS the markup this whole convention is built on, so bounding it would
bound the retain-as-record mechanism itself.  What it gets instead is a number.

A7 is an asymmetry worth stating rather than fixing.  This control has no fence
rule at all: a ` ``` ` line is not `#`, not `>` and not blank, so fenced content
is swept up as an ordinary paragraph and CHECKED.  Its sibling
`onethird_mgcd04_declared_strike_control.py` skips fences deliberately.  The two
controls therefore disagree about whether a fence is data, and this one is on the
fail-closed side of that disagreement, so it is left alone and recorded here.

THE RULE THE BOUNDS ARE SET BY.  MAX_QUOTED_LINES and MAX_EXEMPT_LINES are the
MEASURED REACH at the tree that introduced them, with no headroom, and that is
deliberate.  A bound with slack does not close H1: mg-9a19's M4 appends ONE line
to an 11-line sub-paragraph, so any cap of 12 or more still lets it through --
the same evasion, one line further along.  Set at the reach, the bound is exact
in the way mg-9a19 confirmed the label bound is exact (missed AT the bound,
caught one line past it), and growth is CHECKED rather than tolerated.  The cost
is that legitimately lengthening a quoting sub-paragraph puts its tail into
checked text; the run prints the headroom on every channel so that is visible
before it bites, and raising a bound is a one-line change with a finding attached
-- which is the same contract as adding a BASELINE entry.

BASELINE: EMPTY, as of 2026-07-31 (mg-069f).  This control was written with two
known-live sites as an explicit baseline -- §3.2's "Equivalently" and §5
recommendation 2's converse, the two sites mg-8a71 finding F1 recorded as still
asserting a refuted claim in body text.  The baseline was F1 made executable, not
a tolerance: it was built to fail when a site DISAPPEARED, forcing a re-baseline
to zero once F1 was fixed.  mg-069f struck both at the site, the control failed
with "baseline site disappeared" exactly as designed, and the baseline is now
empty.  From here the control is a plain assertion: the refuted inference is
asserted in live body text NOWHERE in this document, and any reappearance --
including §2.3's struck sentence returning to live text -- fails.

POPULATION.  One file, all of it, and the script now PROVES that rather than
asserting it: every line of `docs/OneThird-L1b-Spread-Locality.md` is classified
into exactly one of {paragraph, quote, heading, exempt-annotation, blank}, the
buckets are printed, and the run asserts they sum to the file's line count.  Not
a sample.  Headings were silently dropped before mg-069f -- used as section
labels and never scanned -- while this paragraph claimed "all of it"; that is the
same NAMED-vs-SWEPT defect this control's own subject matter is about, so it is
recorded rather than quietly fixed.

ONE FILE IS STILL THE POPULATION, AND THAT IS ITS OWN LIMIT.  mg-0242 finding G1
was a block in `docs/OneThird-mgd112-DroppedVerdict-Closeout.md` that declared a
sentence struck and did not strike it -- the exact defect the paragraph above
closed, one document over from where this control looks, so this control could
not see it.  The population is deliberately not widened here: mg-0242 measured a
corpus-wide run of THESE signatures at ~94% false positive, because audit
documents discuss refuted claims in tables and prose the convention has no way to
mark.  What generalises is not the signature but the STRUCTURE -- "a sentence
that declares a strike must carry the markup" is content-free -- and that check
is now corpus-wide in `scripts/onethird_mgcd04_declared_strike_control.py` (2
baselined hits over 242 documents, and it bites at bb1cb9b where G1 is live).
Read the two together: this one asks whether a named claim is
live in one document; that one asks whether any document in the corpus declares a
strike it did not make.

USAGE
    onethird_mg8a71_live_claim_control.py [path]        # default: the doc in-repo
Demonstration against a commit where the defect IS present:
    git show 1b00147^:docs/OneThird-L1b-Spread-Locality.md > /tmp/pre.md
    onethird_mg8a71_live_claim_control.py /tmp/pre.md   # -> exit 1, §2.3 flagged
"""

import re
import sys

DOC = "docs/OneThird-L1b-Spread-Locality.md"

# Two kinds of marked blockquote, and they are NOT treated the same (mg-069f).
#
# EXEMPT: commentary ABOUT the refuted claim — an annotation has to quote and
# discuss the inference to diagnose it, so signatures fired there would be pure
# false positives.  Skipped — but only as far as the quotation runs, and never
# past MAX_EXEMPT_LINES (mg-cd04, mg-0242 G2; before that, skipped ENTIRELY on
# the strength of the label, for a block of any length).
#
# STRIKE: a block retaining a refuted claim as a record.  These are NOT skipped.
# They are checked after inline ~~struck~~ spans are removed, so a block that
# merely *declares* STRUCK while leaving the sentence unstruck still fails.
# Before mg-069f a strike block was skipped on the strength of its label alone,
# and a mutant that deleted the ~~ markup and kept the label passed.
EXEMPT_MARKERS = ("ANNOTATION", "RE-DERIVATION")
STRIKE_MARKERS = ("~~", "STRUCK")

# A1 — the bound on the ONE exemption granted on a label's word alone: the
# label's own sub-paragraph (mg-cd04).  A label is a line or two; 6 is generous
# against every marker in this corpus and far short of the 53-line block mg-0242
# found a three-line label covering.
MAX_LABEL_LINES = 6

# A2 — the bound on a QUOTATION-BACKED sub-paragraph (mg-9d7b, closing mg-9a19
# finding H1).  mg-cd04's comment here used to end "so no further global cap is
# needed", and that sentence was the defect: backing a sub-paragraph with a
# quotation was treated as backing every line of it, at any length, so a refuted
# sentence appended to one stayed exempt (mg-9a19 M4 -> exit 0).
#
# 11 is the longest quotation-backed sub-paragraph in this document, measured,
# with no headroom — see THE RULE THE BOUNDS ARE SET BY in the module docstring.
# A cap of 12 would leave M4 passing, because M4 appends exactly one line.
MAX_QUOTED_LINES = 11

# A3 — the block-level total the docstring has promised since mg-cd04 and which
# did not exist until mg-9d7b.  Bounds the exempt TEXT lines of one EXEMPT block
# (A1 + A2 together); a block's own blank `>` lines are A4 and are not text, so
# they do not spend it.  27 is the largest such total in this document (the
# 44-line block at §5: 1 label line + 26 quotation-backed).  Past it, every
# further sub-paragraph is checked however well it quotes.
MAX_EXEMPT_LINES = 27

# What makes a sub-paragraph of an EXEMPT block commentary rather than body text:
# it QUOTES the thing it is commenting on.  A struck span, or a quoted sentence
# long enough not to be a stray pair of quote marks.  Deliberately NOT inline
# code — `m_x` appears in nearly every line of this corpus, so accepting it would
# hand the exemption straight back.
QUOTATION = re.compile(r'~~.+?~~|"[^"\n]{8,}"|“[^”\n]{8,}”', re.DOTALL)

# Signatures of the refuted inference.  Each is (id, description, predicate).
SIGNATURES = [
    ("S1-jensen-falsifier",
     "Jensen step used to turn a large m_x into a (B) failure",
     lambda t: "jensen" in t and "m_x" in t
               and ("(b) fails" in t or "Θ(n²)" in t or "theta(n^2)" in t)),
    ("S2-hinges-on-degree",
     "lemma (B) said to 'hinge on' capping the per-element degree m_x",
     lambda t: "hinges on" in t and "m_x" in t),
    ("S3-equivalently-degree",
     "chain-cross question equated with the max_x m_x question",
     lambda t: "equivalently" in t and "max_x m_x" in t),
    ("S4-nonexistence-converse",
     "non-existence of the chain-cross asserted to BE (B) (converse over-read)",
     lambda t: re.search(r"non-existence\s+\*?is\*?\s+\(b\)", t) is not None),
]

# (signature id, section) pairs tolerated as live.  EMPTY since mg-069f struck
# the two mg-8a71 F1 sites at the site; see the module docstring.  Adding to this
# set is how a future reader would tolerate a live refuted claim — so don't,
# without a finding that says why.
BASELINE = set()

# An inline ~~struck~~ span is marked text, not live text.
INLINE_STRIKE = re.compile(r"~~.+?~~", re.DOTALL)


def sub_paragraphs(block):
    """Half-open (start, end) index pairs of a blockquote's own sub-paragraphs.

    A blockquote's internal blank lines are `>` or `>` + whitespace; markdown
    keeps them inside the block, which is exactly how a 53-line block ends up
    with one label at the top and six paragraphs of body text under it.
    """
    subs = []
    i = 0
    n = len(block)
    while i < n:
        if not block[i].lstrip(">").strip():
            i += 1
            continue
        j = i
        while j < n and block[j].lstrip(">").strip():
            j += 1
        subs.append((i, j))
        i = j
    return subs


def exempt_partition(block, channels=None):
    """Split an EXEMPT blockquote into (exempt lines, checkable sub-paragraphs).

    mg-cd04 (mg-0242 finding G2).  The label used to exempt `len(block)`, whatever
    that was.  Three rules replace that, and between them every exempt line is now
    either close to the label or backed by its own markup, AND bounded:

      * the LABEL's own sub-paragraph is exempt on the label's word alone — that
        is what a label is — but only for MAX_LABEL_LINES lines.  This is the one
        unbacked exemption left, and it is the one mg-cd04 bounded;
      * every OTHER sub-paragraph is exempt only if it carries a QUOTATION.  An
        annotation earns its exemption by quoting the claim it diagnoses; a
        sub-paragraph that quotes nothing is body text wearing a label three
        lines up, which is precisely the mg-0242 G2 blind spot;
      * a quotation-backed sub-paragraph is exempt for at most MAX_QUOTED_LINES
        lines, and one block's exempt text totals at most MAX_EXEMPT_LINES
        (mg-9d7b, mg-9a19 finding H1).  Backing a sub-paragraph with a quotation
        used to back every line of it at any length, which is the same
        marker-with-no-bound shape one level in.

    Judged per sub-paragraph rather than as a prefix run, deliberately: a genuine
    annotation interleaves quoting paragraphs with non-quoting ones (§2.3's
    mg-1fdb block does), and cutting the run at the first non-quoting paragraph
    would merge every quotation after it into one checked unit and fire on the
    quotations themselves.  Per sub-paragraph, each is judged on its own markup —
    and the appended-tail mutant is still caught, because the mutant quotes
    nothing.

    And bounded by LENGTH rather than by which lines the quotation physically
    touches, also deliberately, also measured: exempting only the lines a
    QUOTATION span covers and checking the rest was tried first and fires
    `S2-hinges-on-degree` on a false positive at line 502 of the audited document.
    Prose here is hard-wrapped, so a quotation and the commentary that earns it
    interleave line by line.  The docstring said so before this was implemented;
    it was right, and the attempt is recorded in this repair's PREDICTIONS as E3.

    `channels`, if given, accumulates a line count per exemption channel so the
    caller can print what each one skipped.

    Returns (n_exempt_lines, [(start, end), ...]) over indices into `block`.
    """
    if channels is None:
        channels = {}

    def note(bucket, k=1):
        channels[bucket] = channels.get(bucket, 0) + k

    subs = sub_paragraphs(block)
    blanks = sum(1 for b in block if not b.lstrip(">").strip())
    if not subs:
        note("A4_blank", len(block))
        return len(block), []          # nothing but blank quote lines
    n_exempt = 0
    checkable = []
    spent = 0                          # exempt TEXT lines used by this block
    for idx, (start, end) in enumerate(subs):
        size = end - start
        if idx == 0:
            cap, bucket = MAX_LABEL_LINES, "A1_label"
        else:
            text = " ".join(b.lstrip("> ").rstrip() for b in block[start:end])
            if not QUOTATION.search(text):
                checkable.append((start, end))
                continue
            cap, bucket = MAX_QUOTED_LINES, "A2_quoted"
        hard = min(size, cap)                       # what the per-sub bound allows
        allow = max(0, min(hard, MAX_EXEMPT_LINES - spent))
        n_exempt += allow
        spent += allow
        note(bucket, allow)
        if size > hard:                             # clipped by A1/A2's own bound
            note(bucket + "_over_bound", size - hard)
        if hard > allow:                            # clipped by the block total
            note("A3_over_block", hard - allow)
        if allow < size:
            # the tail past the bound is ordinary body text and is CHECKED
            checkable.append((start + allow, end))
    # the block's own blank lines are exempt bookkeeping, not text
    note("A4_blank", blanks)
    n_exempt += blanks
    # A3 is a PER-BLOCK bound, so the useful number is the largest block total,
    # not the sum of them.  Summing was this reporter's own first defect: it
    # printed 70 against a bound of 27 and read like a breach.
    channels["A3_block_max"] = max(channels.get("A3_block_max", 0), spent)
    channels["A3_blocks"] = channels.get("A3_blocks", 0) + 1
    return n_exempt, checkable


def live_paragraphs(lines, coverage=None, channels=None):
    """Yield (start_line_no, section_heading, paragraph_text) for checkable text.

    EXEMPT blockquotes (ANNOTATION / RE-DERIVATION) are dropped here; everything
    else — plain paragraphs, headings, unmarked display quotes, and STRIKE
    blockquotes — is yielded, and `scan` strips inline ~~struck~~ spans before
    applying the signatures.

    `coverage`, if given, is a dict that accumulates a line count for every
    disposition, so the caller can assert that the population NAMED is the
    population SWEPT.  Every line of the file lands in exactly one bucket.
    """
    if coverage is None:
        coverage = {}
    if channels is None:
        channels = {}

    def count(bucket, k=1):
        coverage[bucket] = coverage.get(bucket, 0) + k

    def note(bucket, k=1):
        channels[bucket] = channels.get(bucket, 0) + k

    section = "(preamble)"
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.startswith("#"):
            section = line.strip()
            # headings are CHECKED too, not just used as labels: a section title
            # is body text a reader reads (mg-069f — before this, headings were
            # silently dropped while the docstring claimed "one file, all of it")
            count("heading")
            yield i + 1, section, line.strip()
            i += 1
            continue
        if line.startswith(">"):
            # consume the whole blockquote block, decide live/marked once
            j = i
            block = []
            # maximal run of '>' lines; a blank line ENDS the block, so a display
            # quote is never merged with the annotation quote that follows it
            while j < n and lines[j].startswith(">"):
                block.append(lines[j])
                j += 1
            head = " ".join(block[:3]).lower()
            exempt = any(mk.lower() in head for mk in EXEMPT_MARKERS)
            # mg-cd04: the label no longer exempts the block.  It exempts a
            # bounded label sub-paragraph plus whichever sub-paragraphs back
            # themselves with a quotation, each bounded (mg-9d7b); the rest are
            # ordinary quote units.
            if exempt:
                # A8 (mg-9d7b) — the marker is looked for in block[:3]; the label
                # exemption is granted to sub-paragraph 0.  Those are different
                # spans, and when they differ sub-paragraph 0 is exempt on the
                # strength of a label it does not carry.  Reported, not repaired:
                # narrowing detection to sub-paragraph 0 would change which
                # blocks are exempt at all, which is a bigger change than the
                # finding warrants.  0 occurrences in this document.
                _subs = sub_paragraphs(block)
                if _subs:
                    _s, _e = _subs[0]
                    _head0 = " ".join(block[_s:_e]).lower()
                    if not any(mk.lower() in _head0 for mk in EXEMPT_MARKERS):
                        note("A8_label_not_in_sub0", _e - _s)
                n_exempt, checkable = exempt_partition(block, channels)
                count("exempt_annotation", n_exempt)
                for a, b_ in checkable:
                    count("quote", b_ - a)
                    text = " ".join(x.lstrip("> ").rstrip() for x in block[a:b_])
                    if text.strip():
                        yield i + 1 + a, section, text
            else:
                count("quote", j - i)
                text = " ".join(b.lstrip("> ").rstrip() for b in block)
                if text.strip():
                    yield i + 1, section, text
            i = j
            continue
        if line.strip() == "":
            count("blank")
            i += 1
            continue
        # a plain paragraph
        j = i
        para = []
        while j < n and lines[j].strip() != "" and not lines[j].startswith((">", "#")):
            para.append(lines[j])
            j += 1
        count("paragraph", j - i)
        yield i + 1, section, " ".join(p.rstrip() for p in para)
        i = j


def scan(path):
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    lines = raw.split("\n")
    hits = []
    n_live = 0
    coverage = {}
    channels = {}
    for lineno, section, text in live_paragraphs(lines, coverage, channels):
        n_live += 1
        # inline ~~strikethrough~~ is the retain-as-record convention at sentence
        # granularity; drop those spans before testing what the text asserts.
        # A5 (mg-9d7b) — this is an exemption channel and it is measured here:
        # unbounded by design, because it IS the markup, but no longer silent.
        for m in INLINE_STRIKE.finditer(text):
            span = m.group(0)
            channels["A5_inline_strike"] = channels.get("A5_inline_strike", 0) + 1
            channels["A5_inline_strike_chars"] = (
                channels.get("A5_inline_strike_chars", 0) + len(span))
            channels["A5_inline_strike_longest"] = max(
                channels.get("A5_inline_strike_longest", 0), len(span))
        low = INLINE_STRIKE.sub(" ", text).lower()
        for sig_id, desc, pred in SIGNATURES:
            if pred(low):
                hits.append((sig_id, section, lineno, desc, text[:150]))
    # A5 is counted again over the RAW file, before paragraphs are formed, so a
    # span that straddles a structural boundary is not lost to the flattening
    channels["A5_raw_spans"] = len(INLINE_STRIKE.findall(raw))
    channels["A5_raw_markers"] = raw.count("~~")
    # A7 — fenced lines, which this control does NOT exempt.  Counted so the
    # asymmetry with the declared-strike control has a number rather than a note.
    channels["A7_fence_lines_CHECKED"] = sum(
        1 for l in lines if l.lstrip().startswith(("```", "~~~")))
    # the population NAMED must be the population SWEPT: every line accounted for
    assert sum(coverage.values()) == len(lines), (
        f"coverage gap: {sum(coverage.values())} lines classified of {len(lines)}"
    )
    return len(lines), n_live, hits, coverage, channels


def print_channels(channels, total):
    """A5's number, A2's headroom, A8's mismatches — every route out, priced.

    mg-9d7b.  The standard this repair is held to: an exemption that reports its
    own reach is acceptable, an exemption that is silent is not.  So every
    channel prints, including the ones that skipped nothing — a zero is a
    measurement and an absent line is not.
    """
    g = channels.get
    print("  EXEMPTION CHANNELS — every route by which a line leaves this check")
    print(f"    A1 label sub-paragraph          {g('A1_label', 0):>5} lines exempt   "
          f"BOUNDED  {MAX_LABEL_LINES}/sub-paragraph"
          + (f"   [{g('A1_label_over_bound', 0)} clipped -> CHECKED]"
             if g("A1_label_over_bound", 0) else ""))
    print(f"    A2 quotation-backed sub-para    {g('A2_quoted', 0):>5} lines exempt   "
          f"BOUNDED  {MAX_QUOTED_LINES}/sub-paragraph   <- mg-9a19 H1"
          + (f"   [{g('A2_quoted_over_bound', 0)} clipped -> CHECKED]"
             if g("A2_quoted_over_bound", 0) else ""))
    print(f"    A3 block exempt-text total      {g('A3_block_max', 0):>5} lines exempt   "
          f"BOUNDED  {MAX_EXEMPT_LINES}/block   (largest of {g('A3_blocks', 0)} blocks; "
          f"headroom {MAX_EXEMPT_LINES - g('A3_block_max', 0)})"
          + (f"   [{g('A3_over_block', 0)} clipped -> CHECKED]"
             if g("A3_over_block", 0) else ""))
    print(f"    A4 blockquote blank `>` lines   {g('A4_blank', 0):>5} lines exempt   "
          f"not text")
    print(f"    A5 inline ~~struck~~ spans      {g('A5_raw_spans', 0):>5} spans        "
          f"  UNBOUNDED BY DESIGN — it IS the markup")
    print(f"         reach                      {g('A5_inline_strike_chars', 0):>5} chars "
          f"in checked units, longest {g('A5_inline_strike_longest', 0)}, "
          f"{g('A5_raw_markers', 0)} raw `~~` markers")
    print(f"    A6 population                       1 document      UNBOUNDED BY SCOPE "
          f"— argued in mg-cd04, see the docstring")
    print(f"    A7 fenced code                  {g('A7_fence_lines_CHECKED', 0):>5} fence lines  "
          f"NOT A CHANNEL HERE — fenced text is CHECKED")
    print(f"    A8 label not in sub-paragraph 0 {g('A8_label_not_in_sub0', 0):>5} lines        "
          f"  reported; detection reads block[:3]")
    left = g("A1_label", 0) + g("A2_quoted", 0) + g("A4_blank", 0)
    print(f"    -> {left} of {total} lines left the check by an exemption "
          f"({100.0 * left / total:.1f}%).  A5 and A6 are unbounded and PRINTED; "
          f"0 channels unbounded and silent.")


def print_reach():
    """What a green run here does and does NOT mean (mg-0242 finding G4).

    The arc removed refuted claims from live body text FIVE ways and named ONE
    as the standard.  This control sees only whether the CLAIM IS LIVE, so four
    of the five look identical to it -- and mg-0242's instruction was that if the
    control can only see one, it must SAY SO AT THE POINT IT REPORTS, otherwise
    "no un-struck claims" is read as "no unremediated claims".  The matrix below
    is measured by mutation in
    scripts/onethird_mg1d03_remediation_instruments.py, which fails if this
    statement and that measurement drift apart.
    """
    print()
    print("  REACH — what a PASS here does NOT mean (mg-0242 G4):")
    print("    5 remediation instruments are in use in this arc: strike-at-site")
    print("    (the STANDARD), rewrite-in-place, rewrite + annotation, deletion")
    print("    declared as a strike, and none (flagged and routed).")
    print("    This control detects only whether the CLAIM IS LIVE.  Measured by")
    print("    mutation: strike-at-site, rewrite-in-place, rewrite + annotation")
    print("    and an UNDECLARED DELETION all leave it at exit 0 and are")
    print("    indistinguishable to it; only a claim left LIVE trips it.  An")
    print("    unmade DECLARED strike is caught by a different instrument")
    print("    (onethird_mgcd04_declared_strike_control.py), and that is the one")
    print("    boundary between instruments any control in CI can see.")
    print("    So: PASS = 'no refuted claim is live in this one document'.")
    print("    PASS is NOT 'every refutation was remediated', and it is NOT")
    print("    'remediated to the standard'.")


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DOC
    total, n_live, hits, coverage, channels = scan(path)
    print("=" * 78)
    print("mg-8a71 live-claim control — the refuted m_x-falsifier inference")
    print("=" * 78)
    print(f"file      : {path}")
    checked = total - coverage.get("blank", 0) - coverage.get("exempt_annotation", 0)
    print(f"population: {total} lines, ALL classified — "
          f"{coverage.get('paragraph', 0)} paragraph + {coverage.get('quote', 0)} quote + "
          f"{coverage.get('heading', 0)} heading = {checked} CHECKED, "
          f"{coverage.get('exempt_annotation', 0)} exempt (ANNOTATION / RE-DERIVATION), "
          f"{coverage.get('blank', 0)} blank")
    print(f"            -> {n_live} checkable units; inline ~~struck~~ spans dropped "
          f"before matching")
    print(f"signatures: {len(SIGNATURES)}; baseline: {len(BASELINE)} tolerated live sites")
    print()
    print_channels(channels, total)
    print()
    found = set()
    for sig_id, section, lineno, desc, snippet in hits:
        state = "BASELINE" if (sig_id, section) in BASELINE else "*** NEW ***"
        found.add((sig_id, section))
        print(f"  [{state}] {sig_id} @ line {lineno}  ({section})")
        print(f"            {desc}")
        print(f"            > {snippet.strip()}")
    if not hits:
        print("  no live assertion of the refuted inference found — the whole file")
    print()
    new = found - BASELINE
    gone = BASELINE - found
    for sig_id, section in sorted(new):
        print(f"  FAIL: NEW live site  {sig_id} in {section}")
    for sig_id, section in sorted(gone):
        print(f"  FAIL: baseline site disappeared (re-baseline this control): "
              f"{sig_id} in {section}")
    print_reach()
    print("=" * 78)
    if new or gone:
        print("RESULT: FAIL — the live-claim set differs from the recorded baseline.")
        return 1
    print("RESULT: PASS — the refuted inference is asserted in live body text at NO")
    print("        site in this document.  The two sites mg-8a71 finding F1 recorded")
    print("        as outstanding (§3.2's 'Equivalently', §5 rec 2's converse) were")
    print("        struck at the site by mg-069f; §2.3's struck sentence has not")
    print("        returned to live body text.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
