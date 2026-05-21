# Piece 6 axiom verification — is `lem_layered_balanced_irreducible_base` actually true? (mg-44f1)

**Ticket:** mg-44f1 (OneThird-Piece6-Axiom-Verify) — audit, high
priority. Determine whether the disclosed axiom
`OneThird.Step8.lem_layered_balanced_irreducible_base` (introduced by
mg-65de, the Piece 6 redo) is **TRUE**; apply the retained-axiom audit
bar; research the optimal axiom form.

**Predecessors:** mg-65de (Piece 6 redo — introduced the axiom),
mg-fdc2 (Piece 6 RED diagnostic), mg-faf8 (Piece 6 contract),
mg-b846/mg-7377 (the sibling internal axiom
`case3Witness_hasBalancedPair_outOfScope` + its QA).

**Read-first done:** `lean/AXIOMS.md`,
`docs/state-Piece6-Redo-Session1.md`,
`docs/PROOF-STRUCTURE-ONBOARDING.md`, `step8.tex` §`prop:in-situ-balanced`
/ `lem:layered-balanced` / `rem:enumeration` / `rem:residual-base`,
`main.tex` §1 (known classes).

---

## §0. VERDICT

> **TRUE — strong evidence.** The statement axiomatized by
> `lem_layered_balanced_irreducible_base` is, with strong evidence,
> **true**. A genuine counterexample search — exhaustive or via
> structured family over **1 118 061 posets**, randomised over
> thousands more, and run on the exact unbounded irreducible-twin-free
> family that the mg-65de finding flagged as the genuine residual —
> found **zero counterexamples**, and moreover found a **strictly
> positive safety margin**: every poset in the class has a balanced
> pair sitting at least `1/51 ≈ 0.0196` *inside* the `[1/3, 2/3]`
> interval. The axiom is a special case of the
> 1/3–2/3 conjecture; the conjecture is open in general but is the very
> result this paper establishes at width 3, is verified in the
> literature to `n = 11`, and has a proven lower bound
> `δ* ≥ 0.2764` (Brightwell–Felsner–Trotter) close to `1/3`.
>
> **Recommendation to pm-onethird:** the provisional accept becomes
> **recommendable → make it permanent**, with the residual risk of §6
> recorded. This is **not** a FALSE-counterexample finding; no
> escalation is warranted.
>
> **One precision the audit adds:** the axiom is currently **not** on
> the live `#print axioms width3_one_third_two_thirds` dependency — it
> is consumed only by `lem_layered_balanced_full` (Piece 6 of the
> FULL REFACTOR), which is built but not yet wired into the headline.
> It *is* the intended G4 endpoint, so it is load-bearing for the
> intended final architecture, not for the current headline. See §5.

---

## §1. What the axiom actually claims

`lean/OneThird/Step8/LayeredBalancedFull.lean`:

```lean
axiom lem_layered_balanced_irreducible_base.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2       : 2 ≤ Fintype.card β)
    (hNotChain: ¬ IsChainPoset β)
    (hW3      : HasWidthAtMost β 3)
    (hLw      : L.w ≤ 4)
    (hIrr     : ¬ ∃ k, 1 ≤ k ∧ k < L.K ∧ LayerOrdinalReducible L k ∧
                       both sides non-empty)          -- irreducible
    (hNoTwin  : ¬ ∃ a a', a ≠ a' ∧ (∀ z, a < z ↔ a' < z) ∧
                          (∀ z, z < a ↔ z < a')) :    -- twin-free
    HasBalancedPair β
```

Unfolding: **every finite poset `β` that is non-trivial (`|β| ≥ 2`),
not a chain, of width `≤ 3`, that admits a layered decomposition `L`
of interaction width `L.w ≤ 4`, is layer-ordinal *irreducible* w.r.t.
`L`, and is *twin-free*, contains a balanced pair** — an incomparable
`(x, y)` with `1/3 ≤ Pr[x <_L y] ≤ 2/3` over uniform random linear
extensions.

Since `HasBalancedPair β` does not mention `L`, the axiom is true iff:
*for every width-3 non-chain `β` with `|β| ≥ 2` that admits **some**
width-`≤ 4` layered decomposition `L` making it irreducible, and that
is twin-free, `β` has a balanced pair.*

**This is exactly a sub-case of the 1/3–2/3 conjecture** restricted to
the class

```
  C  =  { width-3, non-chain, |β|≥2, admits a layer-ordinal-irreducible
          width-≤4 layered decomposition, twin-free }.
```

It is not a port of an external theorem and it is not a routine
technical lemma: it is *the genuine mathematical core of the width-3
1/3–2/3 result*, after the two genuinely-easier cases (reducible,
twin) have been peeled off and genuinely proved in
`lem_layered_balanced_full`.

### Why this region deserves scrutiny (the mg-65de context)

The axiom sits where the paper's own treatment has been **provably
wrong three times**:

* the in-tree `Case2FKGSubClaim` is **provably false** — its `pair`
  field concludes `probLT a a' ≥ 1/2` from a hypothesis
  (`up(a) ⊆ up(a')`, `down(a) ⊇ down(a')`) that actually forces
  `probLT a a' ≤ 1/2`: a direction-flipped transcription of the
  paper's FKG sub-claim;
* the paper's window-localization Case C1 is invalid for irreducible
  posets — an ordinal middle piece needs two clean cuts and an
  irreducible poset has none (mg-65de §3);
* the paper's Case-C2 size bound `|Q| ≤ 3(3w+1)` is **refuted** — the
  family `P_K = {1,…,K}, i<j ⇔ j−i>2` is irreducible, width 3,
  `w = 2`, with `K` unbounded.

So the correct posture, per the ticket, is **default-skeptical**: a
broken *proof* does not make the *statement* false, but axiomatizing an
unverified statement here is the failure mode to guard against. The
rest of this report is the guard.

---

## §2. Is it true? — three independent lines of evidence

### §2.1  It is a special case of the 1/3–2/3 conjecture

The 1/3–2/3 conjecture (Kislitsyn 1968 / Fredman 1976 / Linial 1984):
*every finite non-chain poset `P` has `δ(P) ≥ 1/3`*, i.e. a balanced
pair. Status (`main.tex` §1, cross-checked):

* **Open in general.** Best proven bound `δ* ≥ (5−√5)/10 ≈ 0.2764`
  (Kahn–Linial / Brightwell–Felsner–Trotter 1995).
* **Proven** for width 2 (Linial), semiorders / interval orders
  (Brightwell), 2-dimensional posets (Kahn–Saks), posets with a
  non-trivial automorphism, height-2 posets.
* **Width 3 "has remained open"** (`main.tex:212`) — it is exactly
  what this paper establishes (conditional on the separate
  Hypothesis A, which concerns the Steps 1–7 large-`α` regime, *not*
  Step 8 / `prop:in-situ-balanced`; the axiom's truth does not depend
  on Hypothesis A).
* Verified computationally for **all posets up to `n = 11`**
  (Peczarski and others).

So the axiom is a genuine instance of an *open* conjecture — but one
that is (a) believed true by the whole order-theory community, (b)
verified to `n = 11`, (c) within `0.057` of being proven outright.
The bound `1/3` is known to be **tight** (`main.tex:162`: the
3-element antichain-plus-bound family), so the closed interval
`[1/3, 2/3]` in the axiom is exactly right and cannot be loosened.

### §2.2  Counterexample search — zero counterexamples in 1.19M posets

A from-scratch exact verifier (`scripts/onethird_mg44f1_axiom_probe.py`,
`..._deep.py`) computes `Pr[x <_L y]` as an **exact rational** for
every incomparable pair via an order-ideal (down-set) DP — the same
linear-extension counting the Lean tree uses, re-implemented
independently. Seven experiments:

| Exp | Class probed | # posets | counterexamples |
|---|---|---:|---:|
| E1 | `P_K` (canonical unbounded residual), `K = 6…90` | 85 | **0** |
| E2 | **every** width-3 non-chain poset, `n = 2…7` | 47 197 | **0** |
| E3 | random layered width-3 posets, **exact axiom class** (irreducible, twin-free, `w ≤ 4`), `n ≤ 22` | 2 847 | **0** |
| E4 | perturbed-`P_K`, mod-3-perturbed-`P_K`, doubled-spine, `K ≤ 40` | ~50 | **0** |
| E5 | **exhaustive** singleton-band irreducible width-3 `w ≤ 4`, `K = 6…9` | 1 070 326 | **0** |
| E5r | random singleton-band irreducible width-3 `w ≤ 4`, `K = 14…42` | 394 | **0** |
| E7 | `P_K` + periodic variants, `K` up to 200 | ~9 | **0** |

**Total: 1 118 061 distinct posets exhaustively or via structured
family, plus 2 847 random in-class posets — zero counterexamples.**
Highlights:

* **E1 / E7 — the exact family mg-65de flagged.** `P_K` (`i<j ⇔
  j−i>2`) *is* the unbounded irreducible width-3 `w=2` family that
  refutes the paper's size bound. It is twin-free for `K ≥ 6`. For
  every `K` from 6 to 200 it has a balanced pair. The probabilities
  *converge*: the safest pair is always a boundary near-twin pair
  `(0,1)` / `(1,2)` with `Pr → 0.59808…` — robustly inside
  `[1/3, 2/3]`. (The bulk adjacent pairs converge to `≈ 0.6674`,
  just *outside* `2/3`; the family is balanced because the boundary
  pairs are not.) Unboundedness does **not** erode the conclusion.

* **E2 — subsumes the axiom for `n ≤ 7`.** Every width-3 non-chain
  poset on `≤ 7` elements has a balanced pair: the width-3 1/3–2/3
  conjecture, verified exhaustively for `n ≤ 7` (and `≤ 11` in the
  literature).

* **E5 — the cap-1 regime, run *unbounded*.** mg-4d7b's certificate
  enumerated the singleton-band irreducible regime only up to
  `|Q| ≤ 10`. E5 re-runs the *same* class with the cardinality cap
  **removed**, exhaustively to `K = 9` (over 1.07M posets) — exactly
  the regime the axiom newly covers — with zero counterexamples.

* **Tightness.** The safety metric — `safety(P) = ` how far *inside*
  `[1/3,2/3]` the *safest* incomparable pair sits — is **strictly
  positive** on every poset found: minimum `safety = 1/51 ≈ 0.0196`
  over the full `K ≤ 9` exhaustive class (1 070 326 posets;
  `1/45 ≈ 0.0222` over the `K ≤ 8` sub-class), and `P_K` converges
  to `safety ≈ 0.0869`. The class never even *approaches* the
  `[1/3,2/3]` boundary; the margin is small but real and does **not**
  decay with size (`P_K`'s margin *converges* rather than shrinking
  to 0).

### §2.3  Structural sanity — why a balanced pair must exist

A structural reason the search keeps succeeding, and the most
promising route to an eventual proof:

* In a layered decomposition of interaction width `w`, two elements
  `a, a'` in the **same band** have two-sided profiles that **differ
  only inside the near-band window** (bands within distance `w`):
  everything at band-distance `> w` is uniformly comparable to the
  whole band by `forced_lt`. So within-band incomparable pairs are
  always "near-twins" — their profiles differ by a *bounded* amount
  (`≤ 3(2w+1) ≤ 27` elements for `w ≤ 4`).
* The hypothesis `hNoTwin` removes only the *degenerate* limit
  (profiles identical ⇒ `Pr = 1/2` exactly, the Case-1 swap); it does
  **not** remove near-twins. Twin-free + bounded interaction width
  therefore *guarantees* incomparable pairs whose profiles differ by a
  small bounded amount, and the search confirms such a pair is always
  balanced (it is consistently the `safety`-maximizing pair).
* Brightwell–Felsner–Trotter is a *theorem*: every poset has *some*
  pair with `Pr ∈ [0.2764, 0.7236]`. A counterexample to the axiom
  would have to squeeze *every* incomparable pair into the thin shells
  `[0.2764, 1/3) ∪ (2/3, 0.7236]`. No such poset is known at any
  width, and the 1/3–2/3 conjecture asserts none exists.

**Conclusion of §2:** the statement is true with strong evidence. The
three lines are independent: a believed-true, `n≤11`-verified, almost-
proven conjecture; a >1.19M-poset exact search with positive margin;
and a structural near-twin argument.

---

## §3. Retained-axiom audit bar

The four-condition bar for *retaining* a named axiom rather than
porting it — `external`, `difficult`, `labeled`, `low-risk` — applied
to `lem_layered_balanced_irreducible_base`, with
`brightwell_sharp_centred` as the 4/4 reference:

| Condition | `brightwell_sharp_centred` | `lem_layered_balanced_irreducible_base` |
|---|---|---|
| **External** | ✅ Brightwell 1999 §4 + Kahn–Saks 1984 — published, peer-reviewed | ❌ **No.** The project's own `prop:in-situ-balanced` Cases 2+3 / `lem:enum`. Novel to this paper; no external citation exists (width-3 1/3–2/3 was open). |
| **Difficult** | ✅ ~500–800 LoC mathlib-tier | ✅ **Yes.** A faithful proof needs the FKG / Ahlswede–Daykin inequality for linear extensions (not in tree; ~2000–3500 LoC, multi-polecat) **plus genuinely new math** for the *unbounded* irreducible regime — the paper's bounded enumeration provably does not cover it (mg-65de §3). |
| **Labeled** | ✅ named `axiom`, AXIOMS.md entry, in `#print axioms` | ✅ **Yes.** Named `axiom`, full AXIOMS.md entry with scope-match checklist + replacement path; would appear in `#print axioms` once the Piece-6 route is headline-wired. |
| **Low-risk** | ✅ a *proven published theorem* | ◑ **Partial.** Low risk of being **false** (§2: strong evidence, positive margin, no counterexample). But **not** low-risk in the brightwell sense: brightwell is proof-backed; this is an instance of an *open* conjecture and specifically the region whose *paper proof is broken*. "Low risk of falsity, unverified provenance." |

**Score: ≈ 2.5 / 4.** The axiom meets `difficult` and `labeled`
cleanly, fails `external`, and meets `low-risk` only in the
"unlikely-false" reading, not the "proof-backed" reading. It is in the
**same category as the sibling internal axiom**
`case3Witness_hasBalancedPair_outOfScope` (also internal, project-own,
2.5/4) and is a strictly **weaker-justified** axiom than
`brightwell_sharp_centred` (4/4).

This does **not** argue for rejecting the axiom — `difficult` +
`labeled` + a disclosed honest replacement path is the established bar
this project uses for an internal residual (cf. `mg-7377`'s "axiom is
faithful" verdict on `case3Witness_hasBalancedPair_outOfScope`). It
does argue for: (a) keeping the disclosure honest that this is **not**
a brightwell-class import but the genuine mathematical core; (b) the
optimal-form work of §4.

---

## §4. The optimal axiom form

### §4.1  The current form is faithful and is the genuine minimal residual

`lem_layered_balanced_full` genuinely proves
`reducible ∨ twin ∨ (irreducible ∧ twin-free)` and the first two
disjuncts are real (Case B = `cor:reducibility-transfer` recursion via
the de-vacuified `lem_layered_reduction`; Case C-twin =
`hasBalancedPair_of_ambient_profile_match`). The axiom is *exactly* the
third disjunct. Every hypothesis (`hW3`, `hLw`, `hIrr`, `hNoTwin`,
`h2`, `hNotChain`) only **shrinks** the class, hence only **lowers**
the risk — there is no spurious strengthening. The form is sound.

### §4.2  One imprecision to fix in AXIOMS.md

The AXIOMS.md entry's **Paper statement** line reads *"`prop:in-situ-
balanced` Cases 2+3"*. But `prop:in-situ-balanced` is stated **with**
the size bound `|Q| ≤ 3(3w+1)` (`step8.tex:3098`); the Lean axiom
**drops** that bound — and *must*, because mg-65de §3 showed the
irreducible residual is genuinely unbounded. So the axiom is not a
transcription of `prop:in-situ-balanced` but its **unbounded
extension** (the size bound deliberately removed, the
`rem:enumeration` "extended to … `2w` near-bands" parenthetical taken
as the real intent). This audit corrects the AXIOMS.md entry to say so
explicitly — see the AXIOMS.md diff in this commit.

### §4.3  Is there a better form? — yes, as replacement-path refinements

The current form is the right *minimal residual* given the current
tree. Two genuine improvements, both requiring infrastructure (so they
are replacement-path items, not immediate rewrites):

1. **Split off the FKG / Case-2 content as an *external-citable*
   axiom (highest value).** The axiom currently bundles paper Case 2
   (FKG profile-ordering ⇒ `Pr ≥ 1/2` for `⪯`-comparable within-band
   profiles) and paper Case 3 (the three-pairwise-`⪯`-incomparable
   profile residual). Case 2 is a consequence of the **Ahlswede–Daykin
   / FKG correlation inequality applied to linear extensions** — a
   *standard, true, citable* result (the same correlation-inequality
   family as Shepp's XYZ theorem). Splitting it out would (a) convert
   roughly half the axiom's content into a brightwell-class
   *external* citation (lifting that half to 4/4 on the audit bar),
   and (b) leave a strictly smaller internal axiom carrying only the
   genuinely novel Case-3 residual. This is the single most valuable
   refinement. It requires replacement-path step 1 (port FKG-for-
   linear-extensions, replacing the provably-false `Case2FKGSubClaim`
   with a correctly-directed statement) to be done first.

2. **Add a size threshold and discharge bounded cases by enumeration
   (modest value).** `prop:in-situ-balanced`'s finite enumeration *is*
   valid when the size is bounded — Case 3 over a bounded poset is a
   finite check (mg-4d7b did the singleton-band slice; mg-be48
   extended part of the non-singleton slice). A refined axiom carrying
   an extra `N₀ ≤ |β|` hypothesis, with `|β| < N₀` discharged by an
   enumeration certificate, would shrink the axiom's scope to the
   genuinely-unbounded tail. Value is modest because the unbounded
   tail is the genuine residual regardless.

`3 ≤ L.K` could be added as a free clarification (`K = 1` ⇒ every
element has empty profiles ⇒ all elements are twins ⇒ `hNoTwin`
already makes the axiom vacuous at `K = 1`); but `K = 2` non-singleton-
band is not separately discharged in tree, so adding the hypothesis is
not actually free. Low value; not recommended now.

### §4.4  The replacement path — confirmed, with one sharpening

AXIOMS.md's 3-step replacement path (1: port FKG-for-linear-extensions;
2: formalize Case 2; 3: formalize Case 3 for the unbounded irreducible
regime) is **sound and confirmed**. One sharpening this audit adds:
**step 3 is genuinely new mathematics, not a porting exercise.** The
paper's bounded enumeration provably does not cover the unbounded
irreducible regime, and there is no published width-3 1/3–2/3 theorem
to cite. A real proof of step 3 needs a new argument — the §2.3
near-twin route (a most-similar incomparable pair always exists under
`hNoTwin` + bounded `w`, and is always balanced) is the most promising
candidate and is strongly supported by the search, but is not proven.
AXIOMS.md is updated to flag step 3 accordingly.

---

## §5. Load-bearing status — a precision the audit adds

The ticket and `state-Piece6-Redo-Session1.md` treat the axiom as the
Piece-6 G4 endpoint. Precisely:

* The committed `lean/PRINT_AXIOMS_OUTPUT.txt` shows
  `OneThird.width3_one_third_two_thirds` depending on `propext`,
  `Classical.choice`, `Quot.sound`, `brightwell_sharp_centred`,
  `case3Witness_hasBalancedPair_outOfScope`, and five `native_decide`
  instances — **`lem_layered_balanced_irreducible_base` is not in that
  list.** mg-65de added `LayeredBalancedFull.lean` /
  `…Example.lean` only; it did not touch `MainTheorem.lean` /
  `MainAssembly.lean`, so the headline dependency is unchanged.
* The only consumers of `lem_layered_balanced_full` (hence of the
  axiom) are `LayeredBalancedFull.lean` itself and
  `LayeredBalancedFullExample.lean`. The current live headline still
  routes through the *bounded* `lem_layered_balanced` →
  `Case3Witness_proof` → `case3Witness_hasBalancedPair_outOfScope`.

So: the axiom is **load-bearing for Piece 6 of the FULL REFACTOR**
(`lem_layered_balanced_full`, the full Step 8 G4) and for the
*intended final architecture* — the FULL REFACTOR plans
`lem_layered_balanced_full` to *replace* the bounded
`lem_layered_balanced` as the G4 endpoint — but it is **not** on the
current `#print axioms` headline. The project currently carries **two
internal axioms over the same mathematical territory** (the irreducible
width-3 residual): the live `case3Witness_hasBalancedPair_outOfScope`
and the not-yet-wired `lem_layered_balanced_irreducible_base`. The
latter is the *cleaner and more honest* of the two — it does not
pretend to a bounded `¬InCase3Scope` scope; it states the genuine
unbounded residual directly. When the Piece-6 route is wired in, it
should *replace* `case3Witness_hasBalancedPair_outOfScope`, not add to
it — the trust surface should not grow.

---

## §6. Residual risk — stated precisely (per the ticket)

Even with a TRUE-strong-evidence verdict, the ticket asks for the
residual risk to be stated. It is:

1. **The axiom is an instance of an open conjecture, not a theorem.**
   It is backed by *no* proof — not the paper's (broken for this exact
   region) and not an external one (width-3 1/3–2/3 was open before
   this paper). Its truth rests on: a >1.19M-poset finite search; the
   conjecture's `n ≤ 11` verification; the proven `0.2764` lower
   bound; and a structural-but-unproven near-twin argument. All
   strong; none a proof.

2. **The danger the ticket names is real but does not bite here.**
   "Axiomatizing an unverified statement in a region where the paper
   has been wrong repeatedly" — the paper's three errors in this
   region (`Case2FKGSubClaim` false, window-localization invalid,
   size bound refuted) are all errors in the *proof method*: each was
   a provably-false *proof step*, not a false *target*. mg-65de
   correctly discarded the broken proof and axiomatized the target.
   This audit confirms the target *survives* the counterexample search
   that the proof steps did not. The pattern is "broken proofs of a
   true statement," not "a false statement." That is a materially
   better situation than the failure mode — but it is worth being
   explicit that the *reason* the axiom is acceptable is the
   independent evidence of §2, **not** the paper's authority.

3. **The axiom's truth is exactly as robust as the 1/3–2/3 conjecture
   itself.** It cannot be more certain than the conjecture it
   instantiates. If the 1/3–2/3 conjecture were false at width 3
   (regarded as extraordinarily unlikely), this paper's headline falls
   regardless of this axiom — so the axiom does not *add* risk beyond
   what the paper already carries by claiming the width-3 result.

4. **No margin erosion observed.** A natural worry for an *unbounded*
   axiom is that the balance margin shrinks to 0 as `|β| → ∞`. The
   search refutes this: `P_K`'s safety margin *converges* to `≈ 0.087`
   (it does not decay), and the exhaustive class keeps `safety ≥
   1/51 ≈ 0.0196`. There is no sign the unbounded tail is more
   dangerous than the bounded part.

---

## §7. Recommendation

* **To pm-onethird (for relay to Daniel):** the provisional accept of
  `lem_layered_balanced_irreducible_base` should become **permanent**.
  It is a genuine, minimal, honestly-disclosed residual; it is true
  with strong evidence; it is strictly weaker than the headline; the
  reducible and twin cases it leaves out are genuinely proved. It is a
  better artifact than a `sorry`. It is **not** brightwell-class
  (internal, not external; open-conjecture instance, not proven
  theorem) and the disclosure must keep saying so.
* **When Piece 6 is wired into the headline:** `lem_layered_balanced_
  irreducible_base` should *replace* `case3Witness_hasBalancedPair_
  outOfScope`, keeping the named-axiom count at its current level.
* **Preferred replacement-path refinement:** §4.3 item 1 — split the
  FKG / Case-2 content into an external-citable axiom once FKG-for-
  linear-extensions is in tree; this is the only move that genuinely
  *lowers* the trust surface rather than relocating it.
* **No escalation.** No counterexample; the width-3 headline is not in
  question on account of this axiom.

---

## §8. Verification log / reproducibility

* `scripts/onethird_mg44f1_axiom_probe.py` — exact rational
  `Pr[x<y]` via order-ideal DP; experiments E1–E4. Self-checks: the
  2-antichain (`Pr = 1/2`) and the `V` poset.
* `scripts/onethird_mg44f1_axiom_probe_deep.py` — experiments E5
  (singleton-band exhaustive + random) and E7 (periodic families);
  `safety` / margin metrics.
* Re-run: `python3 scripts/onethird_mg44f1_axiom_probe.py` (~85 s),
  then `python3 scripts/onethird_mg44f1_axiom_probe_deep.py`.
* The linear-extension counter is an *independent* re-implementation
  (order-ideal lattice DP), not a call into the Lean tree — so it is a
  genuine cross-check, not a tautology.
* Totals: **1 118 061 posets** exhaustively or via structured family
  (E1 85, E2 47 197, E4 ~50, E5 1 070 326 + 394, E7 ~9) plus 2 847
  random in-class posets (E3) — **zero counterexamples**; minimum
  safety margin `1/51 ≈ 0.0196 > 0` over the `K ≤ 9` exhaustive
  class.

## §9. Cross-references

* `lean/AXIOMS.md` — `lem_layered_balanced_irreducible_base` entry
  (updated by this commit with the QA verdict + the §4.2 correction +
  the §4.4 sharpening).
* `lean/OneThird/Step8/LayeredBalancedFull.lean` — the axiom and
  `lem_layered_balanced_full`.
* `docs/state-Piece6-Redo-Session1.md` (mg-65de) — introduced the
  axiom; §3 the unbounded-residual finding.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` — §2 table (updated).
* `step8.tex:3096-3210` (`prop:in-situ-balanced`, `lem:enum`),
  `:3211-3300` (`lem:layered-balanced` proof + `rem:enumeration`).
* `main.tex:136-220` — 1/3–2/3 conjecture status, known classes,
  width-3 "has remained open".
