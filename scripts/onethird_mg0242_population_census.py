#!/usr/bin/env python3
"""mg-0242 — census of every poset population the corpus's controls NAME.

WHY THIS EXISTS.  mg-8a71 finding F2 was that a control NAMED 4 469 labelled
posets and SWEPT 404 -- a 6.9x gap, invisible because nobody had called the
helper and counted; the name and the docstring were read instead.  mg-069f fixed
that gap.  This instrument is the audit of the fix, and it obeys the same rule
that produced the finding: for every population a control names, CALL the helper
and COUNT what it enumerates.  No name is trusted, no docstring is trusted, and
the two generators of the "same" population are checked against each other
rather than each against its own comment.

WHAT IT DOES, in five parts:

  (1) CENSUS.  Calls `posets_with_identity_extension`, `all_labelled_posets` and
      `poset_family` from scripts/onethird_mgfccb_direction_check.py, and
      `all_posets` from scripts/onethird_mg8a71_audit_instrument.py, and counts
      posets / (poset, reference-order) pairs / (poset, order, element) triples
      for each.  Compares each count against the number the corpus states.

  (2) CROSS-GENERATOR IDENTITY.  The corpus now has TWO independent all-labelled
      generators, written from different constructions -- one is the S_n-orbit of
      the identity-extension family, the other assigns each unordered pair one of
      three states and filters for transitivity.  Both are asserted to return
      4 469.  Equal COUNTS do not make them the same population.  This checks
      SET equality.  Nobody had.

  (3) LABEL-DEPENDENCE.  The verdict asks whether `all_posets()`'s replacement,
      checked at a LABEL-DEPENDENT property, either sweeps all labellings or
      refuses.  The property used is the sharpest available one: "does P have the
      identity permutation as a linear extension?"  It is 100% true on the small
      family by construction and 404/4 469 = 9.0% on the labelled population, so
      a helper that silently substituted one for the other would report 100%
      instead of 9.0%.  Three call shapes are exercised: keyword omitted,
      label_dependent=True, label_dependent=False.

  (4) THE GUARD'S REACH.  `poset_family` can only enforce the choice at call
      sites that go through it.  Both underlying generators remain public and
      directly callable.  This counts, in the repo, how many call sites go
      through the guard and how many bypass it.

  (5) THE LIVE-CLAIM CONTROL'S OWN POPULATION.  That control's docstring names a
      line count.  This runs its scanner and compares NAMED against SWEPT -- the
      F2 test applied to the script that F2's fix produced.

Exits non-zero if any named population differs from the population enumerated.

Run:  python3 scripts/onethird_mg0242_population_census.py
"""

import ast
import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
NS = (3, 4, 5)

# KNOWN GAPS, recorded as an explicit baseline in the style mg-8a71 used for the
# live-claim control: a gap listed here does not fail the run, and a gap listed
# here DISAPPEARING does -- so repairing one forces a re-baseline instead of
# passing silently.  Adding to this set is how a future reader would tolerate a
# population that is named wrongly; so don't, without a finding that says why.
#
#   G1  docs/OneThird-mg8a71-VerdictRepairs-Closeout.md §6.1 states the
#       live-claim control sweeps "537/537 lines"; it sweeps 539.
#   G2  scripts/onethird_mgfccb_direction_check.py's docstring table labels the
#       404 -> 4 469 POSET row "(6.9x larger)".  4 469/404 = 11.06x.  6.9x is the
#       ratio of PAIRS (6.87x) and TRIPLES (6.90x), not of posets.
BASELINE = {
    "closeout §6.1: live-claim control lines named vs swept",
    "direction_check docstring: poset-row ratio named vs computed",
}

FAILURES = []
SEEN_GAPS = set()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def check(label, named, counted, baseline_key=None):
    """Record a NAMED-vs-COUNTED comparison; never silently accept."""
    ok = named == counted
    mark = "OK " if ok else ("BASE" if baseline_key in BASELINE else "GAP")
    print(f"  [{mark:<4}] {label:<54} named {named!s:>26}  counted {counted!s:>26}")
    if not ok:
        if baseline_key in BASELINE:
            SEEN_GAPS.add(baseline_key)
        else:
            FAILURES.append(f"{label}: named {named}, counted {counted}")
    elif baseline_key in BASELINE:
        FAILURES.append(
            f"BASELINE GAP CLOSED — re-baseline this control: {baseline_key}")
    return ok


# ------------------------------------------------------------------ part 1 ---


def census_identity_family(dc):
    """Count what posets_with_identity_extension ACTUALLY yields."""
    per_n, pairs, triples = {}, 0, 0
    for n in NS:
        c = 0
        for p in dc.posets_with_identity_extension(n):
            c += 1
            les = list(p.linear_extensions())
            pairs += len(les)
            triples += len(les) * n
        per_n[n] = c
    return per_n, sum(per_n.values()), pairs, triples


def census_labelled_family(dc):
    per_n, pairs, triples = {}, 0, 0
    for n in NS:
        c = 0
        for p in dc.all_labelled_posets(n):
            c += 1
            les = list(p.linear_extensions())
            pairs += len(les)
            triples += len(les) * n
        per_n[n] = c
    return per_n, sum(per_n.values()), pairs, triples


def census_audit_instrument(ai):
    """The audit instrument's own generator: frozensets of strict pairs."""
    per_n, pairs, triples = {}, 0, 0
    for n in NS:
        c = 0
        for rel in ai.all_posets(n):
            c += 1
            les = ai.linear_extensions(n, rel)
            pairs += len(les)
            triples += len(les) * n
        per_n[n] = c
    return per_n, sum(per_n.values()), pairs, triples


# ------------------------------------------------------------------ part 3 ---


def has_identity_extension(rel_pairs):
    """A genuinely LABEL-DEPENDENT property: is 0 < 1 < ... < n-1 an extension?

    Relabelling a poset changes the answer, so any sweep that quietly restricts
    to one labelling class reports the wrong number.  It is the sharpest probe
    available here because it is exactly the property that DEFINES the smaller
    family: 100% on it by construction, 9.0% on the labelled population.
    """
    return all(a < b for a, b in rel_pairs)


def label_dependence_probe(dc):
    print()
    print("(3) LABEL-DEPENDENCE — the replacement helper at a label-dependent property")
    print("    property: 'the identity permutation is a linear extension of P'")
    print("    (label-dependent: relabelling changes the answer)")

    # (a) keyword omitted -- does it refuse?
    refused = None
    try:
        dc.poset_family(3)
        refused = False
    except TypeError as exc:
        refused = True
        print(f"  [OK ] keyword omitted            -> REFUSES: TypeError: {exc}")
    if not refused:
        print("  [GAP] keyword omitted            -> did NOT refuse")
        FAILURES.append("poset_family accepts a call without label_dependent")

    results = {}
    for flag in (True, False):
        tot = hits = 0
        for n in NS:
            for p in dc.poset_family(n, label_dependent=flag):
                tot += 1
                if has_identity_extension(p.less):
                    hits += 1
        results[flag] = (hits, tot)
        pct = 100.0 * hits / tot
        print(f"  [   ] label_dependent={flag!s:<5}       -> {hits}/{tot} = {pct:5.1f}%")

    truth = results[True]
    wrong = results[False]
    print(f"  TRUE answer (all labellings swept)         : {truth[0]}/{truth[1]}"
          f" = {100.0*truth[0]/truth[1]:.1f}%")
    print(f"  answer if the small family is substituted  : {wrong[0]}/{wrong[1]}"
          f" = {100.0*wrong[0]/wrong[1]:.1f}%")
    factor = wrong[1] and truth[1] / wrong[1]
    print(f"  => label_dependent=True SWEEPS ALL LABELLINGS ({factor:.2f}x the small"
          f" family); the keyword is mandatory, so a caller cannot fail to choose.")
    if truth[1] != 4469:
        FAILURES.append(f"label_dependent=True swept {truth[1]}, not 4469")
    if wrong[0] != wrong[1]:
        FAILURES.append("identity-extension property is not 100% on the small family")
    return truth, wrong


# ------------------------------------------------------------------ part 4 ---


GENERATORS = ("posets_with_identity_extension", "all_labelled_posets")


def guard_reach():
    """How many call sites go through poset_family, and how many bypass it?

    Parsed with `ast`, not grepped, so docstrings, comments and the `def` lines
    themselves are not miscounted as call sites, and a call INSIDE the helper
    that defines the family (which is not a bypass) is separated from a call by
    an outside consumer (which is).
    """
    print()
    print("(4) THE GUARD'S REACH — poset_family is advisory unless every caller uses it")
    guarded, internal, bypass = [], [], []
    for path in sorted((ROOT / "scripts").glob("*.py")):
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"))
        except SyntaxError:
            continue
        stack = []

        def walk(node, enclosing):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                enclosing = node.name
            if isinstance(node, ast.Call):
                fn = node.func
                name = (fn.attr if isinstance(fn, ast.Attribute)
                        else fn.id if isinstance(fn, ast.Name) else None)
                rec = (path.name, node.lineno, enclosing or "<module>")
                if name == "poset_family":
                    guarded.append(rec)
                elif name in GENERATORS:
                    (internal if enclosing in GENERATORS + ("poset_family",)
                     else bypass).append(rec)
            for child in ast.iter_child_nodes(node):
                walk(child, enclosing)

        walk(tree, None)
        del stack

    def show(title, rows):
        print(f"  {title:<52}: {len(rows)}")
        for f, i, enc in rows:
            print(f"      {f}:{i}  (in {enc})")

    mine = [r for r in bypass if r[0] == pathlib.Path(__file__).name]
    others = [r for r in bypass if r[0] != pathlib.Path(__file__).name]
    show("call sites via poset_family(...)", guarded)
    show("calls inside the family helpers (not a bypass)", internal)
    show("this census's own deliberate direct calls (it must count each)", mine)
    show("BYPASSES by a real consumer", others)
    bypass = others
    print("  note: both generators remain public module-level names, so the guard")
    print("        binds current callers by construction and future ones only by")
    print("        convention.  That is a real but bounded residual, stated here")
    print("        because the closeout states the guard as if it were total.")
    return len(guarded), len(bypass)


# ------------------------------------------------------------------ part 5 ---


CLOSEOUT = "docs/OneThird-mg8a71-VerdictRepairs-Closeout.md"


def live_claim_control_population(lc):
    """The F2 test, applied to the script F2's fix produced.

    The number is NAMED in the closeout's own named-vs-swept table (§6.1), which
    is the table whose entire purpose is to report this comparison -- so that is
    where it is read from, not from the script, which names only "the file's line
    count" and is therefore true by construction.
    """
    print()
    print("(5) THE LIVE-CLAIM CONTROL'S OWN POPULATION — F2's test applied to F2's fix")
    total, n_live, hits, coverage = lc.scan(str(ROOT / lc.DOC))
    text = (ROOT / CLOSEOUT).read_text(encoding="utf-8")
    m = re.search(r"\*\*(\d+)/(\d+) lines\*\*", text)
    named = int(m.group(2)) if m else None
    print(f"  {CLOSEOUT} §6.1 NAMES : {named} lines")
    print(f"  the control actually SWEEPS         : {total} lines")
    print(f"  buckets: {coverage}")
    checked = total - coverage.get("blank", 0) - coverage.get("exempt_annotation", 0)
    print(f"  of which CHECKED {checked} / {total} = {100.0*checked/total:.1f}%;"
          f"  EXEMPT {coverage.get('exempt_annotation', 0)}"
          f" = {100.0*coverage.get('exempt_annotation', 0)/total:.1f}%"
          f" (granted per-block from 3 label lines, no length bound)")
    check("closeout §6.1: live-claim control lines named vs swept", named, total,
          "closeout §6.1: live-claim control lines named vs swept")
    return named, total, coverage


def docstring_ratio(dc_path):
    """The '(6.9x larger)' label on the docstring's POSET row (part of F2's fix)."""
    print()
    print("(6) THE RATIO THE REPAIR'S OWN DOCSTRING PUTS ON ITS POSET ROW")
    text = pathlib.Path(dc_path).read_text(encoding="utf-8")
    m = re.search(r"tot \|\s*(\d+)\s*\|\s*(\d+)\s*\((\d+(?:\.\d+)?)x larger\)", text)
    if not m:
        print("  no '(Nx larger)' label found on the totals row")
        return None
    small, big, named = int(m.group(1)), int(m.group(2)), float(m.group(3))
    computed = round(big / small, 1)
    print(f"  docstring totals row: {small} -> {big}, labelled '{named}x larger'")
    print(f"  {big}/{small} = {big/small:.4f}  -> {computed}x")
    print(f"  6.9x is the ratio of PAIRS (43842/6385 = {43842/6385:.4f}) and of")
    print(f"  TRIPLES (218166/31625 = {218166/31625:.4f}), not of posets.")
    check("direction_check docstring: poset-row ratio named vs computed",
          named, computed,
          "direction_check docstring: poset-row ratio named vs computed")
    return named, computed


# --------------------------------------------------------------------- main ---


def demonstrate(rev):
    """Run the NAME-vs-COUNT test against a revision where F2 is still present.

    A control that has only ever been run where it passes is not a control.  At
    2697c07 (mg-8a71's HEAD, before mg-069f) the helper is still called
    `all_posets` and its docstring still says "All posets on n labelled
    elements", while it enumerates 404.  The census must report that as a gap.
    """
    print("=" * 96)
    print(f"DEMONSTRATION — the same test at {rev}, where the F2 defect is present")
    print("=" * 96)
    with tempfile.TemporaryDirectory() as td:
        path = pathlib.Path(td) / "old_direction_check.py"
        blob = subprocess.run(
            ["git", "show", f"{rev}:scripts/onethird_mgfccb_direction_check.py"],
            capture_output=True, text=True, cwd=ROOT, check=True).stdout
        path.write_text(blob, encoding="utf-8")
        old = load("old_dc", path)
        gen = getattr(old, "all_posets", None) \
            or getattr(old, "posets_with_identity_extension")
        doc = (gen.__doc__ or "").strip().split("\n")[0]
        counted = sum(1 for n in NS for _ in gen(n))
        print(f"  helper name     : {gen.__name__}")
        print(f"  its docstring   : {doc!r}")
        print(f"  posets ENUMERATED by calling it, n = 3,4,5 : {counted}")
        print(f"  posets its NAME and docstring assert       : 4469 (A001035)")
        gap = counted != 4469
        if gap:
            print(f"  => GAP of {4469 / counted:.2f}x — F2, reproduced by COUNTING")
            print("     rather than by reading the helper's name or its docstring.")
        else:
            print("  => no gap")
        return gap


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--demonstrate":
        return 0 if demonstrate(sys.argv[2]) else 1

    dc_path = ROOT / "scripts/onethird_mgfccb_direction_check.py"
    dc = load("dc", dc_path)
    ai = load("ai", ROOT / "scripts/onethird_mg8a71_audit_instrument.py")
    lc = load("lc", ROOT / "scripts/onethird_mg8a71_live_claim_control.py")

    print("=" * 96)
    print("mg-0242 population census — every population a control NAMES, COUNTED")
    print("=" * 96)
    print()
    print("(1) CENSUS — helpers called, not read")

    per_n, tot, pairs, triples = census_identity_family(dc)
    print(f"  posets_with_identity_extension  per-n: {per_n}")
    check("identity-extension family: posets", 404, tot)
    check("identity-extension family: (poset, order) pairs", 6385, pairs)
    check("identity-extension family: element triples", 31625, triples)
    check("identity-extension family: per-n", [7, 40, 357], [per_n[n] for n in NS])

    lper_n, ltot, lpairs, ltriples = census_labelled_family(dc)
    print(f"  all_labelled_posets             per-n: {lper_n}")
    check("all-labelled family: posets (A001035)", 4469, ltot)
    check("all-labelled family: (poset, order) pairs", 43842, lpairs)
    check("all-labelled family: element triples", 218166, ltriples)
    check("all-labelled family: per-n (A001035)", [19, 219, 4231],
          [lper_n[n] for n in NS])

    aper_n, atot, apairs, atriples = census_audit_instrument(ai)
    print(f"  audit-instrument all_posets     per-n: {aper_n}")
    check("audit instrument: posets", 4469, atot)
    check("audit instrument: (poset, order) pairs", 43842, apairs)
    check("audit instrument: element triples", 218166, atriples)

    ratio = ltot / tot
    print(f"  ratio all-labelled : identity-extension = {ratio:.4f}x"
          f"   ({100.0*triples/ltriples:.1f}% of the triples)")

    print()
    print("(2) CROSS-GENERATOR IDENTITY — same COUNT is not the same POPULATION")
    for n in NS:
        set_a = {frozenset(p.less) for p in dc.all_labelled_posets(n)}
        set_b = {frozenset(rel) for rel in ai.all_posets(n)}
        same = set_a == set_b
        print(f"  n={n}: |orbit-of-identity-family| = {len(set_a)},"
              f"  |3-state filter| = {len(set_b)},  sets equal: {same}")
        if not same:
            FAILURES.append(f"the two all-labelled generators disagree at n={n}: "
                            f"{len(set_a ^ set_b)} posets in the symmetric difference")

    label_dependence_probe(dc)
    guard_reach()
    live_claim_control_population(lc)
    docstring_ratio(dc_path)

    print()
    print("=" * 96)
    print(f"baseline: {len(BASELINE)} known gap(s) tolerated; {len(SEEN_GAPS)} seen")
    for g in sorted(BASELINE):
        print(f"  [{'seen' if g in SEEN_GAPS else 'GONE'}] {g}")
    if FAILURES:
        print(f"RESULT: FAIL — {len(FAILURES)} unbaselined NAMED-vs-COUNTED gap(s):")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print("RESULT: PASS — every population NAMED equals the population COUNTED,")
    print("        except the two doc-level gaps recorded in the baseline above.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
