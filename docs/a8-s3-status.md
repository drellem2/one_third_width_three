# A8-S3 status — `pc-b846` polecat report

**Work item:** `mg-b846` (A8-S3: Case 3 residual — discharge of
`Case3Witness L → HasBalancedPair α` outside `InCase3Scope`).
**Status:** **partial constructive + retained project axiom**, with
honest paper-vs-formalisation diagnosis recorded in `lean/AXIOMS.md`.
**Author.** `pc-b846` polecat, 2026-04-26.

---

## 1. What was supposed to land

> A8-S3 (`mg-b846`) — Discharge `Case3Witness L` (the InSitu one, in
> `Step8.Case3Dispatch` / namespace `Step8.InSitu`) from A8-S1,
> restricted to `¬ InCase3Scope` (since the certificate handles
> `InCase3Scope`).

Mathematical content from the original brief: in a width-3 antichain
`A = {a₁, a₂, a₃}` with `⪯`-incomparable two-sided profiles, two
elements share either `Π⁺` or `Π⁻` modulo a (L2)-permitted permutation.
The shared coordinate then either gives a Case 1 ambient profile match
on a restricted sub-poset (mg-f92d's
`hasBalancedPair_of_ambient_profile_match`) or a Case 2 pair with
aligned one-sided profiles restricted to the bands strictly above/below
the antichain (A8-S2 / `mg-8801`).

Estimated at ~300-600 LoC including the missing mathematical content.

---

## 2. The honest picture (re-confirmed)

The brief's mathematical caveat is on point and re-confirmed during this
polecat session:

> ⚠ Mathematical caveat. This is **new mathematical work beyond what
> the paper provides**. The paper's `rem:enumeration` (`step8.tex:
> 3157-3173`) only **sketches** a structural argument; it doesn't carry
> it out. This ticket needs to flesh out the argument from the sketch.

The sketch in `step8.tex:3157-3173` reads:

> For `w ≥ 1`, the configurations with `|A| = 3` whose profiles form a
> `⪯`-antichain are enumerated modulo the symmetries of (L1); each is
> discharged by exhibiting either a Case 1 symmetric pair (after taking
> into account that two of the three elements must share *some*
> coordinate of the two-sided profile whenever `|Q| ≤ 3(3w+1)` and (L2)
> restricts the profile codomain), or a Case 2 pair with aligned
> one-sided profiles restricted to the bands strictly above (or
> strictly below) the antichain under consideration.

A faithful Lean port requires:

1. **Pigeonhole on shared profile coordinates.** Routine combinatorics.
2. **Band-restricted Case 2 FKG sub-coupling.** Requires the FKG
   primitives of `Mathlib/LinearExtension/FKG.lean` plus a sub-coupling
   restricted to bands strictly above/below the antichain. **Not a
   transcription of the paper proof** — the paper doesn't carry this
   out either; it's a fleshed-out version of the sketch.
3. **Reduction back to Case 1 (mg-f92d) or Case 2 (mg-8801).** Routine
   plumbing.

Step (2) is the substantive new mathematical content. Combined with the
A8-S2 dependency (FKG infrastructure for Case 2, separate work item
`mg-8801`), the full discharge does not fit a single polecat session,
even with the FKG primitives reusable.

---

## 3. What this polecat (`pc-b846`, mg-b846) actually delivers

### 3a. `OneThird/Step8/Case3Residual.lean`

A new file in `lean/OneThird/Step8/` containing:

* `Step8.InSitu.case3Witness_hasBalancedPair_outOfScope` — a project
  axiom that captures the residual claim of `prop:in-situ-balanced`
  Case 3 outside `InCase3Scope`. The axiom signature matches the
  hybrid theorem's wider hypothesis profile plus the typed Case 3
  witness from A8-S1.

* `Step8.InSitu.hasBalancedPair_of_case3_outOfScope` — a `theorem`
  re-export of the axiom, so call-sites cite the result rather than
  the underlying axiom symbol.

* `Step8.InSitu.hStruct_of_case2_discharge` — composed dispatch.
  Given a Case 2 discharge as a hypothesis (filled by A8-S2 /
  `mg-8801` once landed), produces the `hStruct`-shaped function
  `¬ InCase3Scope … → HasBalancedPair α` ready to plug into
  `bounded_irreducible_balanced_hybrid`.

The wiring composes cleanly:

* Case 1 branch: closed via mg-f92d's
  `hasBalancedPair_of_ambient_profile_match` (already in
  `Case3Struct.lean`).
* Case 2 branch: closed via the supplied `case2Discharge` hypothesis
  (consumed from A8-S2 / `mg-8801`).
* Case 3 branch: closed via the
  `case3Witness_hasBalancedPair_outOfScope` axiom (this commit).

Together with A5-G2's `hCert` (Path A — F5a `case3_certificate` for
`InCase3Scope`), these lines wire the full `hStruct + hCert` discharge
into `bounded_irreducible_balanced_hybrid`.

### 3b. `lean/AXIOMS.md` — full disclosure

Adds an entry for `case3Witness_hasBalancedPair_outOfScope` with:

* The paper statement and `rem:enumeration` sketch quotation.
* A scope-match checklist (each hypothesis aligned to the paper).
* "Why this is internal, not external" — distinguishing this axiom
  from the external `brightwell_sharp_centred` (Brightwell 1999 §4).
* "Why retain rather than port" — the band-restricted FKG sub-coupling
  is the substantive new content.
* "Replacement path (open)" — concrete steps for a future polecat or
  contributor to flesh out the sketch.
* "Forum-post disclosure" — what the `mg-b8d4` forum-post draft should
  honestly reflect.

### 3c. `OneThird.lean` import

The new file is imported alongside `OneThird.Step8.Case3Dispatch` so
downstream consumers (A8-S2, A5-G3 / Path C) see it.

---

## 4. What this polecat does NOT do

* It does **not** discharge `Case2Witness L → HasBalancedPair α`
  (deferred to A8-S2 / `mg-8801`).
* It does **not** wire the full `hStruct` slot of
  `bounded_irreducible_balanced_hybrid` directly (deferred to A5-G3 /
  Path C, which composes A8-S1 + A8-S2 + this commit).
* It does **not** flesh out the `rem:enumeration` sketch as a Lean
  proof. The structural pigeonhole + band-restricted FKG sub-coupling
  is genuinely new mathematical work; per the polecat-instruction
  guidance, the gap is honestly retained as a project axiom rather
  than fleshed out under time pressure.

---

## 5. Axiom status delta

Before this commit:

```
'OneThird.width3_one_third_two_thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OneThird.LinearExt.brightwell_sharp_centred]
```

After this commit, the main theorem is unchanged (this file is
imported but its axiom is not yet consumed by the main theorem — it
will become a dependency once A5-G3 / Path C wires `hStruct` into
`lem_layered_balanced`). Any downstream consumer of
`hasBalancedPair_of_case3_outOfScope` or `hStruct_of_case2_discharge`
will pick up the new axiom in its `#print axioms` output, alongside
`brightwell_sharp_centred`.

The `mg-b8d4` forum-post draft should reflect this honestly: two named
axioms, one external (Brightwell), one internal (paper-sketch). All
other uses of the formalism remain sorry-free.

---

## 6. References

* Polecat instructions: `mg-b846` task body.
* `step8.tex` `prop:in-situ-balanced` (`2965-3048`); `lem:enum`
  (`3050-3067`); `rem:enumeration` (`3157-3173`); `rem:residual-base`
  (`3194-3236`).
* `lean/OneThird/Step8/Case3Residual.lean` — this commit.
* `lean/OneThird/Step8/Case3Dispatch.lean` — A8-S1's typed dispatch
  (`mg-48db`).
* `lean/OneThird/Step8/Case3Struct.lean` — Case 1 ambient form
  (`mg-f92d`).
* `lean/AXIOMS.md` — full axiom audit (this commit's entry).
* `docs/a8-status.md` — full mg-A8 status report (mg-f92d's polecat
  output).
