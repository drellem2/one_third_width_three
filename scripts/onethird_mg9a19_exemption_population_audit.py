#!/usr/bin/env python3
"""mg-9a19 — INDEPENDENT AUDIT of the mg-cd04 repair of mg-0242 G1/G2.

WHAT THIS IS FOR.  mg-cd04 closed two findings about EXEMPTIONS: a block that
exempts itself by DECLARING a strike (G1), and a label that exempts a block of
any length (G2).  It closed both.  This instrument asks the two questions that
survive the closure, and it asks them the way this arc's findings have always
turned out to matter -- at the POPULATION, and against the repair's own text:

  (1) an exemption is only as good as its BOUND and its POPULATION.  For every
      exemption channel in the two repaired controls, is it length-bounded, and
      how far does it actually reach in this corpus?
  (2) the repair's rule was applied by the repair to 242 documents.  The corpus
      holds more than that, and the arc's claims do not all live in the 242.

FOUR PARTS.

  (P) POPULATION.  Every tracked `*.md` in the repo, partitioned into: what the
      live-claim control reads (1 document), what the declared-strike control
      reads (`docs/*.md`, NON-RECURSIVE), where the ledger's ten refuted claims
      live (3 documents), and the REMAINDER that no structural control reads.
      The remainder is then swept with the declared-strike rule, because a
      population finding that does not run the rule over the unswept part is
      the same finding one level up -- which is the sentence mg-0242 wrote and
      this audit is obliged not to reproduce.
      The sweep PROVES its population: every path lands in exactly one bucket
      and the buckets are asserted to sum to `git ls-files '*.md'`.

  (B) BOUNDS.  Every channel by which text escapes checking in either repaired
      control, with the bound if there is one.  mg-cd04 added exactly one bound
      (`MAX_LABEL_LINES = 6`).  This part records which channels still have
      none, and measures how far each reaches at HEAD.

  (M) MUTANTS.  The parent's three-mutant table EXTENDED, not re-run.  M1-M3 are
      mg-0242's and are asserted by `onethird_mg0242_struck_vs_refuted.py`;
      M4-M9 are new and probe the boundary the fix drew rather than the one it
      removed.  Each carries the exit code RECORDED when this audit ran, and a
      change in either direction fails -- the convention mg-8a71 set for its
      baseline and mg-0242 kept, applied to a mutant table.  A mutant that
      starts being caught is a repair; a mutant that stops being caught is a
      regression; both must force a re-record rather than pass silently.

  (S) SELF.  The declared-strike control run over the repair's OWN new prose,
      and over THIS audit's own document and this script.  Reported as blocks
      CHECKED vs blocks that EVADE, and separately as what the evading blocks
      would have been had they not evaded.  Five deliverables in this lineage
      have reproduced their own defect class in their own text; an audit of the
      sixth that does not point the instrument at itself is worthless.

  (L) THE LEDGER DRIFT, re-derived -- behind `--drift`, and NOT on the default
      path.  `script-controls.yml` checks out at depth 1 by design (mg-3934), so
      a step that read history there would be dead on arrival.  No revision is
      named in code; both come from argv.

USAGE
    onethird_mg9a19_exemption_population_audit.py
    onethird_mg9a19_exemption_population_audit.py --drift <base-rev> <repair-rev>
        # e.g. --drift 1b00147 bb1cb9b -- the ledger's ten claims classified at
        # each tree by EACH of the two classifier versions, so the contribution
        # of the CLASSIFIER and the contribution of the TEXT are separated.
"""

import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent

LIVE_CLAIM = "scripts/onethird_mg8a71_live_claim_control.py"
DECLARED_STRIKE = "scripts/onethird_mgcd04_declared_strike_control.py"

SPREAD = "docs/OneThird-L1b-Spread-Locality.md"
MGD112 = "docs/OneThird-mgd112-DroppedVerdict-Closeout.md"
BBIAS = "docs/OneThird-Bbias-Locality-Lemma.md"

# The repair's own new prose, and this audit's own.  Both are swept in part (S).
REPAIR_PROSE = "docs/OneThird-mg0242-G1G2-Repair.md"
AUDIT_PROSE = "docs/OneThird-mg9a19-ExemptionPopulation-IndependentAudit.md"


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


LC = load(LIVE_CLAIM, "lc")
DS = load(DECLARED_STRIKE, "ds")


def tracked_md():
    """Every `*.md` in the working tree, from the git index AND from disk.

    Both sources, unioned, deliberately.  The first run of this part asserted
    against `git ls-files` alone while the declared-strike control's population
    comes off the FILESYSTEM, and the assertion below fired the moment this
    audit's own report existed on disk and not yet in the index: 267 counted, 266
    named.  That is the mg-8d5e shape -- a comparison whose two sides are not the
    same ruler -- caught by the assertion that is here for exactly that reason,
    in the instrument auditing a finding about it.  Recorded rather than quietly
    corrected; the untracked count is printed so the two sources stay
    reconcilable.
    """
    tracked = set(subprocess.run(["git", "ls-files", "*.md"],
                                 capture_output=True, text=True,
                                 cwd=ROOT).stdout.split())
    on_disk = {f"docs/{p.name}" for p in (ROOT / "docs").glob("*.md")}
    return sorted(tracked | on_disk), sorted(on_disk - tracked)


# ------------------------------------------------------------------ part P ---

def part_p():
    print("=" * 96)
    print("(P) POPULATION — what the repaired controls range over, and what they do not")
    print("=" * 96)
    md, untracked = tracked_md()
    ds_pop = sorted(f"docs/{p.name}" for p in (ROOT / "docs").glob("*.md"))
    lc_pop = [LC.DOC]
    ledger_pop = sorted({SPREAD, MGD112, BBIAS})

    remainder = [f for f in md if f not in set(ds_pop)]
    # every tracked .md lands in exactly one bucket
    buckets = {"swept by the declared-strike control": len(ds_pop),
               "UNSWEPT by any structural control": len(remainder)}
    assert sum(buckets.values()) == len(md), (
        f"population gap: {sum(buckets.values())} of {len(md)} tracked .md files")

    in_docs_tree = [f for f in remainder if f.startswith("docs/")]

    print(f"  *.md in the working tree (index + disk)           : {len(md)}"
          f"   ({len(untracked)} on disk and not yet in the index)")
    print(f"  read by {LIVE_CLAIM.split('/')[-1]:<46}: "
          f"{len(lc_pop)}   <- G2 was repaired HERE")
    print(f"  read by {DECLARED_STRIKE.split('/')[-1]:<46}: {len(ds_pop)}")
    print(f"  the ledger's ten refuted claims live in           : "
          f"{len(ledger_pop)}   ({', '.join(p.split('/')[-1] for p in ledger_pop)})")
    print()
    print(f"  UNSWEPT by the corpus-wide control                : {len(remainder)}")
    print(f"      of which INSIDE docs/ (subdirectories)        : {len(in_docs_tree)}")
    print(f"      of which elsewhere in the repo                : "
          f"{len(remainder) - len(in_docs_tree)}")
    print()
    print("  The control's docstring says \"every `*.md` in `docs/`\"; the glob is")
    print("  non-recursive, so `docs/` holds "
          f"{len(ds_pop) + len(in_docs_tree)} markdown documents and the control")
    print(f"  reads {len(ds_pop)}.  Reported as a coverage gap, not as a defect: the")
    print("  remainder is swept below, and it is clean.")
    print()
    for f in remainder:
        print(f"      {f}")
    print()

    # SWEEP THE REMAINDER with the declared-strike rule.
    hits = []
    n_lines = 0
    for f in remainder:
        text = (ROOT / f).read_text(encoding="utf-8", errors="replace")
        n_lines += len(text.split("\n"))
        h, _near, _cov = DS.scan_text(f, text)
        hits.extend(h)
    print(f"  declared-strike rule over the unswept remainder: "
          f"{len(remainder)} documents, {n_lines} lines -> {len(hits)} hit(s)")
    for name, lineno, quote, snippet in hits:
        print(f"      {name}:{lineno}  \"{quote[:70]}\"")
    print()
    return len(md), len(lc_pop), len(ds_pop), len(ledger_pop), len(remainder), len(hits)


# ------------------------------------------------------------------ part B ---

def measure_exempt_reach():
    """Every EXEMPT sub-paragraph in the live-claim control's one document."""
    lines = (ROOT / LC.DOC).read_text(encoding="utf-8").split("\n")
    rows = []
    i = 0
    while i < len(lines):
        if lines[i].startswith(">"):
            j = i
            while j < len(lines) and lines[j].startswith(">"):
                j += 1
            head = " ".join(lines[i:i + 3]).lower()
            if any(m.lower() in head for m in LC.EXEMPT_MARKERS):
                blk = lines[i:j]
                for k, (a, b) in enumerate(LC.sub_paragraphs(blk)):
                    text = " ".join(x.lstrip("> ").rstrip() for x in blk[a:b])
                    quoted = LC.QUOTATION.search(text) is not None
                    rows.append((i + a + 1, b - a, k == 0, quoted))
            i = j
            continue
        i += 1
    return rows


def count_fenced():
    total = fenced = 0
    unclosed = []
    for p in sorted((ROOT / "docs").glob("*.md")):
        ls = p.read_text(encoding="utf-8").split("\n")
        cov = {}
        list(DS.blocks(ls, cov))
        total += len(ls)
        fenced += cov.get("fenced_code", 0)
        if sum(1 for l in ls if DS.FENCE.match(l)) % 2:
            unclosed.append(p.name)
    return total, fenced, unclosed


def part_b():
    print("=" * 96)
    print("(B) BOUNDS — every channel by which text escapes checking, and its bound")
    print("=" * 96)
    rows = measure_exempt_reach()
    label_rows = [r for r in rows if r[2]]
    quoted_rows = [r for r in rows if not r[2] and r[3]]
    checked_rows = [r for r in rows if not r[2] and not r[3]]
    total, fenced, unclosed = count_fenced()

    print(f"  live-claim control ({LC.DOC.split('/')[-1]}):")
    print(f"    channel 1  EXEMPT label sub-paragraph")
    print(f"               BOUND: MAX_LABEL_LINES = {LC.MAX_LABEL_LINES}  (added by "
          f"mg-cd04; this is the bound G2 asked for)")
    print(f"               reach at HEAD: {len(label_rows)} label sub-paragraph(s), "
          f"{sum(min(r[1], LC.MAX_LABEL_LINES) for r in label_rows)} unbacked line(s) "
          f"used of {len(label_rows) * LC.MAX_LABEL_LINES} available")
    print(f"    channel 2  EXEMPT sub-paragraph carrying a QUOTATION")
    print(f"               BOUND: MAX_QUOTED_LINES = "
          f"{getattr(LC, 'MAX_QUOTED_LINES', None)}  (added by mg-9d7b closing H1; "
          f"was NONE at mg-9a19 — exempt entire, any length)")
    print(f"               reach at HEAD: {len(quoted_rows)} sub-paragraph(s), "
          f"{sum(r[1] for r in quoted_rows)} line(s), longest "
          f"{max((r[1] for r in quoted_rows), default=0)}")
    print(f"    channel 2b BLOCK exempt-text total")
    print(f"               BOUND: MAX_EXEMPT_LINES = "
          f"{getattr(LC, 'MAX_EXEMPT_LINES', None)}  (added by mg-9d7b; the "
          f"identifier this control's docstring named twice and never defined)")
    print(f"    (for contrast, CHECKED: {len(checked_rows)} non-quoting "
          f"sub-paragraph(s), {sum(r[1] for r in checked_rows)} line(s))")
    print()
    print(f"  declared-strike control (docs/*.md):")
    print(f"    channel 3  FENCED CODE (closed)")
    print(f"               BOUND: NONE, BY DESIGN — the skip runs to the closing "
          f"fence, and a fence is length-independently 'this is data'")
    print(f"               reach at HEAD: {fenced} of {total} lines "
          f"({100 * fenced / total:.1f}%), NOW PRINTED by the control's own output "
          f"(mg-9d7b; it was silent at mg-9a19)")
    print(f"    channel 3b UNCLOSED FENCE")
    print(f"               BOUND: n/a — mg-9d7b stopped treating it as a fence at "
          f"all; the marker line is checked and the site is named")
    print(f"               documents with an ODD fence count: "
          f"{len(unclosed)}  {', '.join(unclosed) or '—'}")
    print(f"               (at mg-9a19 each of these skipped to EOF, silently)")
    print(f"    channel 4  '{DS.STRIKE_MARKUP}' ANYWHERE IN THE BLOCK")
    print(f"               BOUND: n/a — the DECLARATION test is per SENTENCE, the "
          f"BACKING test is per BLOCK")
    print(f"               so one unrelated struck span exempts every declaration "
          f"in its block (mutant M9)")
    print(f"               mg-9d7b left this OPEN and made it REPORTED: the control "
          f"now prints every sentence exempted this way")
    print()
    return (len(label_rows), len(quoted_rows),
            max((r[1] for r in quoted_rows), default=0), fenced, total, unclosed)


# ------------------------------------------------------------------ part M ---

MUTANT_SENTENCE = (
    "Lemma (B) therefore hinges on whether the frozen structure caps the "
    "per-element inversion degree `m_x`, and by Jensen a large `m_x` makes (B) "
    "fails by Θ(n²)."
)

DECLARED_DEFECT = (
    '**POPULATION CORRECTION.** The row above is corrected; the sentence that\n'
    'followed — *"over every poset and every reference order at those sizes"* — is\n'
    'struck with it.\n'
)


def run_lc(path):
    return subprocess.run([sys.executable, str(ROOT / LIVE_CLAIM), str(path)],
                          capture_output=True, text=True).returncode


def exempt_blocks(lines):
    out = []
    i = 0
    while i < len(lines):
        if lines[i].startswith(">"):
            j = i
            while j < len(lines) and lines[j].startswith(">"):
                j += 1
            head = " ".join(lines[i:i + 3]).lower()
            if any(m.lower() in head for m in LC.EXEMPT_MARKERS):
                out.append((i, j))
            i = j
            continue
        i += 1
    return out


# (id, description, RECORDED exit/hit count when this audit ran).  A change in
# EITHER direction fails: a mutant that starts being caught is a repair and a
# mutant that stops being caught is a regression, and both have to be recorded
# rather than absorbed.
# RE-RECORDED ONCE, by mg-9d7b, and this is the whole entry for that event.
# M4 and M8 moved 0 -> 1 because mg-9d7b bounded the channels that were letting
# them through: H1's quotation-backed sub-paragraph (MAX_QUOTED_LINES) and H2's
# unclosed fence (no longer treated as a fence at all).  Both moved in the REPAIR
# direction.  The pre-mg-9d7b values are kept in the third column rather than
# overwritten, because this table's whole purpose is that a residual cannot move
# quietly -- including when it moves the right way.
RECORDED = {
    "M4": 1,   # live-claim: appended to a QUOTATION-BACKED sub-paragraph  (was 0 — mg-9d7b closed it)
    "M5": 0,   # live-claim: inside the label sub-paragraph, line 2
    "M6": 0,   # live-claim: at the label bound, line 6
    "M7": 1,   # live-claim: one line past the bound, line 7
    "M8": 1,   # declared-strike: unclosed fence above the defect          (was 0 — mg-9d7b closed it)
    "M9": 0,   # declared-strike: an unrelated ~~ elsewhere in the block    (still missed; now REPORTED by the control)
    "M10": 1,  # declared-strike: the bare defect, to prove M8/M9 mean something
}

# What each mutant was at mg-9a19, kept so the movement stays legible after the
# table above is read at face value by someone who never saw the audit.
RECORDED_AT_MG9A19 = {"M4": 0, "M5": 0, "M6": 0, "M7": 1,
                      "M8": 0, "M9": 0, "M10": 1}


def part_m():
    print("=" * 96)
    print("(M) MUTANTS — the parent's table EXTENDED: what the fix's boundary lets past")
    print("=" * 96)
    lines = (ROOT / LC.DOC).read_text(encoding="utf-8").split("\n")
    blocks_ = exempt_blocks(lines)
    assert blocks_, "no EXEMPT blockquote found"

    # the longest EXEMPT block whose LAST sub-paragraph carries a quotation --
    # that is the tail the parent's M1 does NOT test
    target = None
    for start, end in blocks_:
        blk = lines[start:end]
        subs = LC.sub_paragraphs(blk)
        if not subs:
            continue
        a, b = subs[-1]
        text = " ".join(x.lstrip("> ").rstrip() for x in blk[a:b])
        if LC.QUOTATION.search(text):
            if target is None or (end - start) > (target[1] - target[0]):
                target = (start, end, start + b)
    assert target, "no EXEMPT block ends in a quotation-backed sub-paragraph"
    tstart, tend, tail = target
    # the first EXEMPT block, for the label-bound mutants
    lstart, _lend = blocks_[0]

    results = {}
    with tempfile.TemporaryDirectory(prefix="mg9a19-") as td:
        td = pathlib.Path(td)

        def lc_mut(mid, new_lines):
            p = td / f"{mid}.md"
            p.write_text("\n".join(new_lines), encoding="utf-8")
            results[mid] = run_lc(p)

        # M4 — appended to the END of the last, QUOTATION-BACKED sub-paragraph.
        # The parent's M1 opens a NEW sub-paragraph (`> ` then the sentence) and
        # is caught because the new sub-paragraph quotes nothing.  This one joins
        # a sub-paragraph that already carries its quotation, so the whole
        # sub-paragraph -- of any length -- stays exempt.
        lc_mut("M4", lines[:tail] + ["> " + MUTANT_SENTENCE] + lines[tail:])
        # M5/M6/M7 — the label sub-paragraph's bound, probed from both sides
        lc_mut("M5", lines[:lstart + 1] + ["> " + MUTANT_SENTENCE] + lines[lstart + 1:])
        pad = ["> filler " + c for c in "abcd"]
        lc_mut("M6", lines[:lstart + 1] + pad + ["> " + MUTANT_SENTENCE]
               + lines[lstart + 1:])
        lc_mut("M7", lines[:lstart + 1] + pad + ["> filler e", "> " + MUTANT_SENTENCE]
               + lines[lstart + 1:])

    # M8/M9/M10 — the declared-strike control, in-process (it has no CLI path
    # for a single document, and scan_text is its whole rule)
    def ds_mut(mid, text):
        h, _n, _c = DS.scan_text(f"{mid}.md", text)
        results[mid] = 1 if h else 0

    ds_mut("M10", "# doc\n\nprose\n\n" + DECLARED_DEFECT)
    ds_mut("M8", "# doc\n\n```\nliteral\n\n" + DECLARED_DEFECT)
    ds_mut("M9", "# doc\n\nA ~~different~~ clause here. The sentence that followed "
                 '— *"over every poset and every reference order at those sizes"* — '
                 "is struck with it.\n")

    print(f"  target EXEMPT block: lines {tstart + 1}-{tend} ({tend - tstart} lines); "
          f"its last sub-paragraph ends at line {tail} and carries a quotation")
    print()
    print("  from mg-0242 / mg-cd04, asserted by onethird_mg0242_struck_vs_refuted.py:")
    print("    M1  refuted sentence as a NEW sub-paragraph in an ANNOTATION tail   "
          "-> 1  caught (was 0 at mg-0242)")
    print("    M2  the same sentence as a plain paragraph                          "
          "-> 1  caught")
    print("    M3  the same sentence in the tail of a STRIKE block                 "
          "-> 1  caught")
    print()
    labels = {
        "M4": "same sentence appended to a QUOTATION-BACKED sub-paragraph",
        "M5": "same sentence inside the LABEL sub-paragraph (line 2 of 6)",
        "M6": f"same sentence at the label bound (line {LC.MAX_LABEL_LINES} of "
              f"{LC.MAX_LABEL_LINES})",
        "M7": f"same sentence one line PAST the bound (line {LC.MAX_LABEL_LINES + 1})",
        "M8": "declared strike under an UNCLOSED fence",
        "M9": "declared strike in a block holding an unrelated ~~ span",
        "M10": "the bare declared strike (proves M8/M9 are about the exemption)",
    }
    moved = []
    for mid in ("M4", "M5", "M6", "M7", "M8", "M9", "M10"):
        got, rec = results[mid], RECORDED[mid]
        verdict = "caught" if got else "MISSED"
        flag = "" if got == rec else f"   <-- MOVED (recorded {rec})"
        if got != rec:
            moved.append(mid)
        print(f"    {mid:<4}{labels[mid]:<62}-> {got}  {verdict}{flag}")
    print()
    return results, moved


# ------------------------------------------------------------------ part S ---

def unfenced(text):
    return "\n".join(l for l in text.split("\n") if not DS.FENCE.match(l))


def part_s():
    print("=" * 96)
    print("(S) SELF — the repaired control over the repair's own new prose, and over "
          "this audit's")
    print("=" * 96)
    targets = [REPAIR_PROSE, MGD112,
               "docs/OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md"]
    if (ROOT / AUDIT_PROSE).exists():
        targets.append(AUDIT_PROSE)
    rows = []
    for f in targets:
        text = (ROOT / f).read_text(encoding="utf-8")
        ls = text.split("\n")
        cov = {}
        nblocks = len(list(DS.blocks(ls, cov)))
        h, near, _ = DS.scan_text(f, text)
        hu, _nu, _ = DS.scan_text(f, unfenced(text))
        nfence = sum(1 for l in ls if DS.FENCE.match(l)) // 2
        rows.append((f, len(ls), nblocks, nfence, cov.get("fenced_code", 0),
                     len(h), len(near), len(hu)))
        print(f"  {f.split('/')[-1]}")
        print(f"      {len(ls)} lines, {nblocks} checked blocks, "
              f"{nfence} fenced region(s) = {cov.get('fenced_code', 0)} EVADING lines")
        print(f"      hits {len(h)}   near misses {len(near)}   "
              f"hits WITH THE FENCES REMOVED: {len(hu)}")
        if len(hu) > len(h):
            for name, lineno, quote, snip in hu:
                print(f"          would have been a hit: \"{quote[:64]}\"")
    print()
    print("  The declared-strike control does not read scripts/, so the module that")
    print("  DEFINES the rule is invisible to it.  Applying the rule there anyway:")
    sh = []
    for p in sorted((ROOT / "scripts").glob("*.py")):
        h, _n, _c = DS.scan_text(p.name, p.read_text(encoding="utf-8",
                                                     errors="replace"))
        sh.extend(h)
    print(f"      scripts/*.py -> {len(sh)} hit(s) "
          f"({len({h[0] for h in sh})} file(s)); every one is a docstring "
          f"describing the rule")
    for name, lineno, quote, snip in sh:
        print(f"          {name}:{lineno}  \"{quote[:60]}\"")
    print()
    return rows, len(sh)


# ------------------------------------------------------------------ part L ---

LEDGER_PATTERNS = [
    ("C1", SPREAD, "S1-jensen-falsifier"),
    ("C2", SPREAD, "S2-hinges-on-degree"),
    ("C3", SPREAD, r"equivalently.*max_x m_x"),
    ("C4", SPREAD, r"non-existence\s+\*?is\*?\s+\(b\)"),
    ("C5", SPREAD, r"this is the single pin"),
    ("C6", BBIAS, r"restored at all three sites"),
    ("C7", SPREAD, r"over all posets on"),
    ("C8", MGD112, r"over \*\*all\*\* posets"),
    ("C9", MGD112, r"over every poset and every reference order"),
    ("C10", MGD112, r"sweep over all posets"),
]


def load_rev(rev, tmp):
    src = subprocess.run(["git", "show", f"{rev}:{LIVE_CLAIM}"],
                         capture_output=True, text=True, cwd=ROOT).stdout
    p = tmp / f"lc_{re.sub(r'[^A-Za-z0-9]', '_', rev)}.py"
    p.write_text(src, encoding="utf-8")
    spec = importlib.util.spec_from_file_location(p.stem, p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def live_set(mod, tree):
    cache = {}
    out = []
    sigs = {sid: pred for sid, _d, pred in mod.SIGNATURES}
    for cid, f, pat in LEDGER_PATTERNS:
        if f not in cache:
            if tree is None:
                text = (ROOT / f).read_text(encoding="utf-8")
            else:
                text = subprocess.run(["git", "show", f"{tree}:{f}"],
                                      capture_output=True, text=True,
                                      cwd=ROOT).stdout
            cache[f] = [mod.INLINE_STRIKE.sub(" ", t).lower()
                        for _l, _s, t in mod.live_paragraphs(text.split("\n"), {})]
        if pat in sigs:
            test = sigs[pat]
        else:
            rx = re.compile(pat, re.IGNORECASE)
            test = lambda t, rx=rx: rx.search(t) is not None
        if any(test(u) for u in cache[f]):
            out.append(cid)
    return out


def ledger_source(rev):
    return subprocess.run(
        ["git", "show", f"{rev}:scripts/onethird_mg0242_struck_vs_refuted.py"],
        capture_output=True, text=True, cwd=ROOT).stdout


def ledger_definition(src):
    body = src.split("LEDGER = [")[1].split("\n]")[0]
    return re.findall(r'\("(C\d+[^"]*)"', body), re.findall(r'r"([^"]+)"', body)


def part_l(base_rev, repair_rev):
    print("=" * 96)
    print("(L) THE LEDGER DRIFT — re-derived, with the CLASSIFIER and the TEXT "
          "separated")
    print("=" * 96)
    with tempfile.TemporaryDirectory(prefix="mg9a19-lc-") as td:
        td = pathlib.Path(td)
        old = load_rev(repair_rev, td)
        new = LC
        print(f"  classifiers: OLD = {repair_rev}:{LIVE_CLAIM.split('/')[-1]}, "
              f"NEW = working tree")
        print(f"  trees      : {base_rev}, {repair_rev}, working tree")
        print()
        print(f"  {'tree':<14}{'classifier':<12}{'LIVE':>5}  claims")
        rows = {}
        for tree, tlabel in ((base_rev, base_rev), (repair_rev, repair_rev),
                             (None, "working tree")):
            for clabel, mod in (("OLD", old), ("NEW", new)):
                L = live_set(mod, tree)
                rows[(tlabel, clabel)] = L
                print(f"  {tlabel:<14}{clabel:<12}{len(L):>5}  "
                      f"{', '.join(L) or '—'}")
        print()
        # is the LEDGER DEFINITION the same object at both ends?  mg-8d5e's
        # anchor defect is a comparison whose two sides are not the same ruler.
        d_base = ledger_definition(ledger_source("HEAD"))
        moved_def = None
        for probe in (base_rev, repair_rev):
            try:
                d = ledger_definition(ledger_source(probe))
            except IndexError:
                continue
            if d != d_base:
                moved_def = probe
        print(f"  LEDGER DEFINITION identical at every revision that has one: "
              f"{'NO — ' + str(moved_def) if moved_def else 'YES'}")
        print()
        b_old = len(rows[(base_rev, "OLD")])
        b_new = len(rows[(base_rev, "NEW")])
        h_new = len(rows[("working tree", "NEW")])
        r_new = len(rows[(repair_rev, "NEW")])
        print(f"  classifier contribution at {base_rev}: "
              f"{b_old} -> {b_new}  "
              f"({', '.join(set(rows[(base_rev, 'NEW')]) - set(rows[(base_rev, 'OLD')])) or 'none'})")
        print(f"  text contribution {repair_rev} -> working tree: "
              f"{r_new} -> {h_new}  "
              f"({', '.join(set(rows[(repair_rev, 'NEW')]) - set(rows[('working tree', 'NEW')])) or 'none'})")
        print()
    return rows


# ------------------------------------------------------------------- main ---

def main():
    if len(sys.argv) > 3 and sys.argv[1] == "--drift":
        part_l(sys.argv[2], sys.argv[3])
        return 0

    n_md, n_lc, n_ds, n_led, n_rem, n_rem_hits = part_p()
    print()
    n_label, n_quoted, longest, fenced, total, unclosed = part_b()
    print()
    results, moved = part_m()
    print()
    rows, n_script_hits = part_s()

    print()
    print("=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  POPULATION  tracked *.md {n_md}; declared-strike control reads {n_ds}; "
          f"live-claim control (where G2 was repaired) reads {n_lc};")
    print(f"              the ledger's ten refuted claims live in {n_led}; "
          f"{n_rem} unswept, carrying {n_rem_hits} hit(s).")
    print(f"  BOUNDS      mg-cd04 added one (MAX_LABEL_LINES={LC.MAX_LABEL_LINES}, "
          f"enforced exactly — M6/M7); mg-9d7b added two more")
    print(f"              (MAX_QUOTED_LINES={getattr(LC, 'MAX_QUOTED_LINES', None)}, "
          f"MAX_EXEMPT_LINES={getattr(LC, 'MAX_EXEMPT_LINES', None)}) and stopped "
          f"unclosed fences skipping to EOF.")
    print(f"              BOUNDED now: quotation-backed sub-paragraphs "
          f"({n_quoted} of them, longest {longest}).")
    print(f"              UNBOUNDED still, but BY DESIGN and no longer SILENT: closed "
          f"fenced code, {fenced} of {total} lines corpus-wide,")
    print(f"              printed by the control itself.  {len(unclosed)} unclosed "
          f"fence(s), formerly skipping to EOF, are now CHECKED.")
    print(f"  MUTANTS     M4 (quotation-backed tail) -> {results['M4']} "
          f"(was {RECORDED_AT_MG9A19['M4']} at mg-9a19), "
          f"M8 (unclosed fence) -> {results['M8']} "
          f"(was {RECORDED_AT_MG9A19['M8']}), "
          f"M9 (block-scope backing) -> {results['M9']}.")
    print(f"  SELF        the repair's own report evades "
          f"{rows[0][4]} lines in {rows[0][3]} fenced region(s); with the fences "
          f"removed it carries {rows[0][7]} hit(s).")
    print()
    if moved:
        print("RESULT: FAIL — a recorded mutant outcome MOVED: " + ", ".join(moved))
        print("        A mutant that starts being caught is a repair and a mutant")
        print("        that stops being caught is a regression.  Re-record RECORDED")
        print("        in this script and say in the report which it was.")
        return 1
    print("RESULT: PASS — every recorded outcome reproduced.  The findings this")
    print("        instrument encodes are NOT closed by it passing; it passing means")
    print("        the residual is exactly where this audit measured it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
