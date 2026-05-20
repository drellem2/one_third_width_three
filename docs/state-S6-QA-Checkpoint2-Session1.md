# State — OneThird S6-QA: Checkpoint 2 audit (mg-e996)

**Ticket:** mg-e996 — OneThird-S6-QA: Checkpoint 2 audit — is the
grounded Steps 1-6 cascade consumable by Piece 2, and did S1-E genuinely
close the Checkpoint-1 gap.
**Phase:** FULL REFACTOR Phase 2, Checkpoint 2 — the hold-the-line
go/no-go gate after Step 6 (Piece 1), gating Piece 2 (S7-A-E
concretisation). Per `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`
§2.1 risk 2 and §3.3 Checkpoint 2.
**Depends:** mg-65af (S6-B — landed).
**Session:** 1.

---

## §0. Verdict — **AMBER** (gap surfaced; re-scope before Piece 2 dispatch)

> **GREEN is not defensible; RED is too strong.** Both parts of the
> charter surface a gap.
>
> **Part 2 first, because it inverts the ticket's own premise.** The
> mg-e996 ticket body states *"Checkpoint 1 AMBER, fixed by S1-E
> mg-c2d7"*. **That is factually wrong.** S1-E (mg-c2d7) was an explicit
> **RED block-and-report** (its own state doc §0). It did *not* close
> the Checkpoint-1 gap — it diagnosed it as a definition-layer bug
> (`IsGoodFiber` G2 = rectangle-convexity, which empties `goodFiberSet`)
> and reported. No subsequent commit re-ported the G2 clause
> (`git log c9ee834..HEAD` = S1-E, S4-C, S6-A, S6-B only). **The
> Checkpoint-1 gap is still open.** `goodFiberSet a0 a1 = ∅` is still
> machine-checked in tree (`interface_part_iv_faithfulness_defect`,
> `Interface.lean:772`); `bounded_interaction` is still the vacuous
> `|Int| ≤ |𝓛(P)|` (`Corollaries.lean:213`).
>
> **Part 1.** The Step 6 grounded forms (`thm_step6_grounded`,
> `cor_pointwise_grounded`, `cascade_steps_1_6_grounded`) are sound,
> sorry-free, axiom-free theorems on concrete BK-graph carrier objects.
> But "consumable by Piece 2" is **only partially** true: the S4
> per-pair bound threads in genuinely (type-compatible, trivially
> composable); one S5 wire (G10) is genuinely invokable; **the S2 `ε₂`
> bookkeeping does not wire into Step 6 at all** (`ε₂` appears in zero
> Step 6 files; no Step 6 file imports Step 2; the grounded chain skips
> G6 `lem:most-good` where `ε₂` enters). Every numeric constant and
> every upstream output is a **free parameter / free hypothesis**; the
> cascade is *not composed end-to-end*; the concrete witnesses use
> **hand-built singleton fibers**, not S1-`thm_interface`-produced ones.

**Severity = AMBER, not RED.** No theorem is false; the Step 6 grounded
layer builds clean (sorry-free, axiom-free — the four predecessor state
docs attest `lake build OneThird` clean; `grep` confirms no `sorry`/`axiom`
anywhere in `Step{1..6}/`). The math is sound (mg-8b95 §7 verified the
paper). The fixes are **bounded re-scopes** (§6): re-port G2 (already
scoped by S1-E §5), ground G6 + wire `ε₂`, compose the cascade
end-to-end with a genuine-object witness. It is not a re-architecture
and not a dead end.

**Severity = AMBER, not GREEN.** Three concrete unresolved items block a
go verdict:

1. **The Checkpoint-1 gap is still open** (Part 2). The mg-8b95
   Checkpoint-1 audit §8.3 and S1-E §5 *both* gated cascade assembly
   behind the G2 re-port. The re-port never landed. S6-A/S6-B assembled
   the cascade and declared "Piece 1 closes" anyway — see finding 4.
2. **The S2 `ε₂` → Step 6 wire is absent** (Part 1, finding 1). S2-B
   §2/§4 *explicitly deferred* the `ε₂ ↔ C₂'` reconciliation to
   "Checkpoint 2"; S6-A/S6-B did not perform it. G6 (`lem:most-good`)
   is still abstract; `badSet` is an opaque parameter.
3. **The cascade is parametric and uncomposed** (Part 1, finding 3).
   `cascade_steps_1_6_grounded` takes every upstream output as a free
   hypothesis with free constants; its concrete witness hand-builds
   the fibers; the grounded forms have **zero downstream consumers**.
   End-to-end consumability with genuine cascade objects is unverified
   and is actively threatened by item 1.

**Recommendation (§6): do NOT dispatch Piece 2.** File the G2 re-port
(S1-E §5 forward action) first; then ground G6 + wire `ε₂`; then compose
the cascade with at least one genuine-object concrete witness so
satisfiability is compiler-checked rather than asserted.

---

## §1. Scope and method

**Charter (ticket mg-e996), two parts.**

* **Part 1 — the standard Checkpoint 2.** Is the abstract Step 6
  scaffold (the most-built-out of Steps 1-6) genuinely consumable by
  the grounded S2/S4/S5 outputs? Verify four specific wires: S2 `ε₂` →
  Step 6 per-fiber input; S4 per-pair incompatibility → Step 6
  aggregation; S5 richness witnesses invokable in the expansion branch
  without adapters; S6-A/S6-B produce dichotomy + pointwise-uniformity
  in **concrete form on the BK-graph foundation**, not abstract
  scaffolding needing downstream adapters.
* **Part 2 — re-verify the Checkpoint-1 fix is genuine.** Confirm S1-E
  genuinely closed the gap: `goodFiberSet` genuinely non-empty;
  part-(iv) bad-set bound the genuine `O(|Z|·t²)` form; `bounded_interaction`
  + `cor:overlap`/`cor:triple-overlap` density corollaries carry genuine
  content. **Probe satisfiability on natural width-3 non-chain inputs,
  not just type-compatibility.**

**Method.** Paper-and-code reading. Read the read-first set
(`PROOF-STRUCTURE-ONBOARDING.md`; scoping doc §2.1/§3.3;
`state-S1234-QA-Checkpoint1-Session1.md`). Read the Step 6 grounded Lean
in full (`Step6/DichotomyGrounded.lean`, `Step6/PointwiseGrounded.lean`)
and the relevant abstract scaffold (`Step6/Assembly.lean` §G7Grounded,
`Step6/ErrorControl.lean`, `Step6/RichnessBound.lean`,
`Step1/Corollaries.lean`, `Step1/Interface.lean` §6). Read the S1-E /
S2-B / S4-C / S5-E / S6-A / S6-B state docs. Verified every "is in tree"
/ "is wired" claim by `grep` and by reading proof bodies, not signatures
or docstrings (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #4).

**Build state.** Worktree on `polecat-mg-e996` off `755d03c` (S6-B).
`grep` confirms **no `sorry` and no `axiom`** anywhere in
`lean/OneThird/Step{1..6}/` (the only textual hits are docstring
"sorry-free" notes). The S2-B / S4-C / S5-E / S6-A / S6-B state docs
each attest `lake build OneThird` clean with `#print axioms` = the three
standard mathlib axioms. A full mathlib rebuild was not re-run — this is
a paper+code audit, docs-only deliverable; the attestations + the
`sorry`/`axiom` grep cover it (same posture as the Checkpoint-1 audit
mg-8b95 §1).

---

## §2. What Piece 1 / the Step 6 grounded forms deliver

`Step6/` carries the full abstract cleared-denominator scaffold of
`step6.tex` (G6-G10 + `thm:step6` + `cor:pointwise`), no `sorry`. On top
of it, two grounded files were landed by Wave-4:

* **S6-A (mg-9576) — `Step6/DichotomyGrounded.lean`.**
  `thm_step6_grounded` (the dichotomy `thm:step6`), `thm_step6_rich_closure_grounded`
  (the low-conductance closure `rem:G5-closes-dichotomy`),
  `thm_step6_rich_closure_grounded_of_firstMoment` (closure with the
  G10 rich-case bound discharged), and the `Fin 3 × Fin 3` non-vacuity
  instance `thm_step6_grounded_concrete`.
* **S6-B (mg-65af) — `Step6/PointwiseGrounded.lean`.**
  `disagreement_mass_eq_double_count` (the `step6.tex` Step-2
  double-counting identity — genuine new content),
  `cor_pointwise_grounded` (`cor:pointwise`), `cascade_steps_1_6_grounded`
  (the "termination point of Piece 1"), and two `Fin 3 × Fin 3`
  instances.

**What is genuine.** The carrier objects are concrete BK-graph data:
`Step4.bkBoundary S` (the real BK boundary), `pairOverlap Fstar`,
`visibility richStar Fstar`, `disagreePairs`, `posCount`/`negCount`/
`minorityCount`. The `step6.tex` Step-2 double-counting identity
`disagreement_mass_eq_double_count` is a real proof (counts triples
`(L,α,β)` two ways). The dichotomy case-split `thm_step6_grounded` and
its closure are genuine `ℕ`-arithmetic — the real content of `thm:step6`
Steps D-E. **This part of Piece 1 is real and sound** — that is why the
verdict is AMBER not RED.

**The defect S6-A itself flagged.** The abstract `Step6.thm_step6`
collides two distinct `M`s (`step6.tex` multiplicity constant vs. overlap
mass). The grounded forms correctly use two variables (`mult` and the
explicit `∑ pairOverlap`). This is handled and is not a Checkpoint-2
gap — noted for completeness.

---

## §3. Part 1 — is the Step 6 scaffold consumable by grounded S2/S4/S5?

The four charter wires, each verified against the Lean.

### §3.1. Finding 1 — the S2 `ε₂` bookkeeping does NOT wire into Step 6

**Verdict: missing wire.**

* `grep -rln "ε₂"` over `lean/OneThird/` returns `Step2/PerFiberGrounded.lean`,
  `Step2/PerFiberGrounded2.lean`, `Step3/LocalSign.lean`,
  `Step7/SignedThreshold.lean`, `Step7/Cocycle.lean` — **and no `Step6/`
  file**. `ε₂` is absent from the entire Step 6 layer.
* **No `Step6/` file imports `OneThird.Step2`** (`grep -rln "import
  OneThird.Step2" lean/OneThird/Step6/` = empty).
* The grounded Step 6 chain starts at **G9** (the summed Step-4 bound):
  `thm_step6_grounded` takes `hSum : c_n·∑_bad w ≤ c_d·mult·|∂_BK S|`
  directly as a hypothesis. The paper's `ε₂` enters Step 6 at **G6**
  (`lem:most-good` / `prop:gap-g1`) — the per-fiber error split that
  *produces* the bad set. `lem_most_good` (G6) exists **only in the
  abstract `Step6/Assembly.lean:100`** and is **not grounded**. The
  grounded chain skips it entirely.
* Consequently `badSet : Finset (Pair × Pair)` in `thm_step6_grounded`
  and `cascade_steps_1_6_grounded` is an **opaque parameter** — the
  `ε₂`-driven good/bad fiber classification (which fibers *are* bad) is
  not connected to anything.
* **S2-B explicitly deferred this.** `state-S2-B-Session1.md` §2 honest
  note: *"the exact reconciliation of the constants (`step6.tex`'s `C₂'`
  vs this port's `K·κ/η`) is a genuine Step-6-porting concern and is
  what Checkpoint 2 (after S6 lands) is for"*; §4 scope boundary lists
  *"The Step 6 reconciliation of the `ε₂` / `C₂'` constants — a
  Checkpoint 2 / S6-porting concern"* as out of S2-B scope. **S6-A and
  S6-B did not pick it up.** S6-A §5 and S6-B §4 state the Step 6 port
  consumes the Step-1/Step-2 outputs "parametrically" — which is
  precisely the observation that the wire was *not* made.

The charter item "verify the S2 `ε₂` bookkeeping wires into the Step 6
per-fiber input" therefore resolves to: **it does not wire in; the
reconciliation S2-B deferred to Checkpoint 2 was never done.**

### §3.2. Finding 2 — the S4 per-pair bound DOES thread in (genuine)

**Verdict: genuinely consumable; type-compatible; trivially composable;
not actually composed.**

* `lem_sum_step4_grounded` (added by S4-C mg-3bca to `Step6/Assembly.lean:256`,
  §2a `G7Grounded`) is a **real grounded bridge**: it takes the grounded
  Step-4 witness family `Step4.witnessFamilyOfPairs S …` on the genuine
  BK boundary `Step4.bkBoundary S`, plus the overlap-counting
  multiplicity `hmult` and the S4-B per-pair input `hPerPair`, and
  produces `c_n·∑_bad w ≤ c_d·M·|∂_BK S|`.
* That output shape is **identical** to `thm_step6_grounded`'s `hSum`
  hypothesis `c_n·∑_bad w ≤ c_d·mult·|∂_BK S|` (`M ↔ mult`). Composition
  `thm_step6_grounded … (lem_sum_step4_grounded …)` is trivial.
* **But it is not done.** No in-tree theorem composes
  `lem_sum_step4_grounded → thm_step6_grounded`; `hSum` is a free
  hypothesis of every grounded Step 6 theorem. `lem_sum_step4_grounded`
  is referenced only in `DichotomyGrounded.lean` *docstrings*, never
  invoked (`grep`).
* S4-C's `lem_sum_step4_grounded_nonvacuous` exercises the bridge on
  `Fin 3 × Fin 3`, so the S4→S6 type-compatibility is genuinely
  witnessed.

This is the soundest of the four wires: the S4 per-pair incompatibility
bound is genuinely consumable by Step 6 aggregation. The only debt is
the (trivial) composition.

### §3.3. Finding 3 — S5 richness: one genuine wire (G10), the rest parametric

**Verdict: G10 invokable without adapters; the first-moment input is a
free hypothesis.**

* `thm_step6_rich_closure_grounded_of_firstMoment` genuinely **invokes**
  `pair_overlap_sum_ge_vol` (G10, `RichnessBound.lean:233`) to discharge
  the rich-case lower bound `c_R²·|S| ≤ M` from the first-moment
  richness `hfirst : c_R·|LP| ≤ ∑_{a∈richStar}|Fstar a|`. G10 is a real
  S5/RichnessBound lemma and is invoked **without an adapter** — this
  charter item is satisfied for G10.
* But `hfirst` itself is a **free hypothesis**. S5-E's
  `thm_step5_assembled` produces a `Step5Richness |LP| fiberMass c_R`
  structure of *matching shape* (`Step5Richness 6 648 9` in the concrete
  instance), so S5→S6 is type-compatible — but the composition is not
  done, and `Fstar`/`richStar` remain free parameters.

### §3.4. Finding 4 — concrete form vs. abstract scaffolding

**Verdict: concrete carrier objects, but everything quantitative is a
free parameter; the cascade is uncomposed; the witnesses are hand-built;
zero downstream consumers.**

* **Constants are all free `ℕ` parameters.** `thm_step6_grounded`,
  `thm_step6_rich_closure_grounded`, `cascade_steps_1_6_grounded` take
  `mult, c_n, c_d, δ_n, δ_d, c_R, t_n, t_d` as unconstrained `ℕ`
  arguments. No theorem ties any of them to the actual Step 4 / Step 5 /
  Step 6 cascade constants.
* **The cascade conclusion is not composed.** `cascade_steps_1_6_grounded`
  takes `hsub, hfirst, hvol, hSum, hLow, hbadW, hbadSub, hNonActive` —
  **every** upstream output — as free hypotheses. It is not built from
  the S1-S5 grounded producers; it is an arithmetic assembly *given* the
  cascade outputs.
* **The concrete witnesses hand-build the fibers.**
  `cascade_steps_1_6_grounded_concrete` and `cor_pointwise_grounded_concrete`
  use `pwFstar := fun _ => {gridLinExt}` and `gridFstar := fun _ => {gridLinExt}`
  — singleton fibers fabricated for the witness, **not** raw/good fibers
  produced by S1's `thm_interface`. This is exactly the dodge mg-8b95 §5
  flagged for Step 2 ("Step 2's non-vacuity witness builds its good
  fiber as a hand-made singleton {L} … not a `rawFiber` produced by
  Step 1").
* **Zero downstream consumers.** `grep` for `thm_step6_grounded`,
  `cor_pointwise_grounded`, `cascade_steps_1_6_grounded`,
  `thm_step6_rich_closure_grounded` outside their own files returns
  nothing. The only importer of `Step6.PointwiseGrounded` is the library
  aggregator `OneThird.lean`. S7 (`Step7/SignConsistency.lean:1015`)
  consumes the **abstract** `OneThird.Step6.cor_pointwise`
  (`Step6/Assembly.lean:520`), not the grounded `cor_pointwise_grounded`.
  So the grounded forms are import-only leaves: their consumability is
  **untested by the compiler**.

So "produces the dichotomy and pointwise-uniformity outputs in concrete
form, not abstract scaffolding needing downstream adapters": the carrier
*objects* are concrete; the *theorems* are genuine. But the form is a
chain of type-compatible-but-uncomposed parametric theorems whose
end-to-end satisfiability on genuine cascade objects is neither composed
nor compiler-checked — which is "abstract scaffolding still needing the
adapters" in every operative sense.

---

## §4. Part 2 — did S1-E genuinely close the Checkpoint-1 gap?

**Verdict: NO. S1-E (mg-c2d7) was a RED block-and-report. The gap is
still open. The ticket body's premise — "Checkpoint 1 AMBER, fixed by
S1-E mg-c2d7" — is factually wrong.**

`state-S1-E-Session1.md` §0: *"Verdict — RED (block-and-report): the
Checkpoint-1 AMBER gap is a definition-layer bug, not an assembly gap."*
S1-E found `IsGoodFiber` G2 is product-order rectangle-convexity, too
strong; it inverts the good/bad partition. S1-E §5: the fix is a **new
S1-A-class ticket** to re-port the G2 clause — *"not in the S1-E budget
or file scope"*.

`git log c9ee834..HEAD` (since S1-E's predecessor) = `7cbe9e2` S1-E,
`b5e2ebc` S4-C, `65fa242` S6-A, `755d03c` S6-B. **No commit re-ports
the G2 clause.** `LocalCoords.lean:200` still reads "(G2) its coordinate
image is order-convex in `ℕ²`" — unchanged.

The three Part-2 sub-questions, each verified in tree:

1. **Is `goodFiberSet` genuinely non-empty?** **NO.**
   `goodFiberSet_a0_a1_eq_empty` (`Interface.lean:740`) and
   `interface_part_iv_faithfulness_defect` (`:772`) machine-check
   `goodFiberSet a0 a1 = ∅` and `badSet a0 a1 = 𝓛(P)` on `Antichain3`
   (a genuine width-3 non-chain poset) — still in tree, no `sorry`, no
   `axiom`. `goodFiberSet` is **empty** for every rich pair with `t ≥ 1`.

2. **Is the part-(iv) bad-set bound the genuine `O(|Z|·t²)` form?**
   **NO.** Not delivered — S1-E §4 item 1 BLOCKED. There is no
   `|Bad| = O(|Z|·t²)` cardinality statement, no strip decomposition.

3. **Do `bounded_interaction` / `cor:overlap` (b) / `cor:triple-overlap`
   (d) carry genuine content?** **NO.** `bounded_interaction`
   (`Corollaries.lean:213`) is still verbatim the vacuous scaffold
   `(interactionLocus x y u v).card ≤ Fintype.card (LinearExt α)` —
   `|Int| ≤ |𝓛(P)|`. Its docstring still says *"it will be tightened …
   once `thm:interface` part (iv) is discharged in a follow-up item."*
   `Corollaries.lean:81` carries the `⚠ AMENDED (S1-E, mg-c2d7)` banner:
   *"the scaffold upgrade is BLOCKED … left as-is."* `cor:overlap` (b)
   and `cor:triple-overlap` (d) density bounds are undelivered.

**The corollary vacuity the ticket warned about has not recurred — it
never went away.** It is the same vacuous scaffold flagged at
Checkpoint 1, still present, now correctly *labelled* vacuous by the
S1-E banner but not fixed.

### §4.1. Why the cascade "does not see" the open S1 gap — and why that is the gap

S6-A §5 and S6-B §4 both argue the S1-E RED finding *"does not block
this port"* because Step 6 consumes the Step-1/Step-2 outputs
**parametrically**. **That argument is internally correct but is the
disease, not the cure.**

The mg-8b95 Checkpoint-1 audit §8.3 and S1-E §5 *both* gated: cascade
*assembly* is blocked until the G2 re-port lands; only *individual*
grounded lemmas may be ported hypothesis-first. S6-A/S6-B nonetheless
landed `cascade_steps_1_6_grounded` — the cascade assembly — and S6-B §0
declares *"Piece 1 closes."*

The reason the S1-E gap appears not to propagate is that **nothing in
the S2/S5/S6 grounded layer ever instantiates a fiber from S1's
`goodFiberSet`.** Every grounded step takes the good-fiber data as a
free parameter (`Fstar`, `TripleFiberData`, `RichFamily`); every
concrete witness hand-builds a non-degenerate singleton fiber (§3.4).
The gap is "localised to the S1 re-port" *only* because the cascade
never touches the genuine S1 output.

This is the **`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #6 pattern**: a
type-clean signature that is structurally unsatisfiable on the genuine
objects. The moment Piece 2 — or any honest end-to-end assembly — tries
to instantiate `Fstar` / `hfirst` / `badSet` with genuine S1→S5 cascade
objects, it meets: `goodFiberSet = ∅` ⇒ degenerate fibers ⇒ `hfirst`
(`c_R·|LP| ≤ ∑|F⋆_α|` with `c_R ≥ 1`) unsatisfiable ⇒ the second moment
`M = 0` ⇒ the cascade conclusion collapses to `0 ≤ 0`. The parametric
port has not removed the gap; it has deferred it to the first honest
consumer.

So **"Piece 1 closes" is an over-claim.** The grounded Step 6 *theorems*
landed and are sound (real, GREEN). But Piece 1 as *"the Steps 1-6
cascade port delivering outputs genuinely consumable by Piece 2"* is not
complete: S1 is broken (G2), S2's `ε₂` is unwired, and the cascade is a
chain of uncomposed parametric theorems whose end-to-end satisfiability
on genuine objects is unverified and is actively threatened by the open
S1 gap.

---

## §5. Satisfiability probe (charter mandate — not a type check)

The charter mandates probing satisfiability on natural width-3 non-chain
inputs. Take `Antichain3` and `Fin 3 × Fin 3`, the genuine width-3
non-chain posets the ports themselves use.

* **`thm_step6_grounded` / `cor_pointwise_grounded` are satisfiable as
  parametric theorems** — the `Fin 3 × Fin 3` instances fire. There is
  **no unsatisfiable delivered signature** in the Step 6 grounded layer.
  This is why the verdict is AMBER, not RED.

* **But the operative cascade instantiation is unsatisfiable on genuine
  S1 objects.** The natural Piece-2 instantiation feeds the Step 6
  `Fstar` from S1's good fibers. On `Antichain3`, S1-E machine-checked
  `goodFiberSet a0 a1 = ∅`. With genuine `Fstar a = ∅`: `visibility = 0`,
  `pairOverlap = 0`, `M = ∑ pairOverlap = 0`, and `hfirst : c_R·|LP| ≤
  ∑|Fstar a| = 0` forces `c_R = 0` — the `c_R = 0` vacuous baseline the
  S5-E witness explicitly avoids (`Step5Richness` with `c_R = 9` is
  hand-built, S5-E §3). The cascade conclusion `t_n·δ_d·∑_A I² ≤ t_d·2·δ_n·M`
  becomes `0 ≤ 0`.

* **The concrete witnesses dodge exactly this.** `cascade_steps_1_6_grounded_concrete`
  uses `pwFstar := fun _ => {gridLinExt}` — a fabricated non-empty
  fiber. It is a genuine *Finset* on a genuine poset, but it is **not**
  an S1-`thm_interface`-produced fiber, so it does not test whether the
  cascade can consume the *genuine* S1 output. It tests only that the
  arithmetic fires given a non-degenerate `Fstar`.

This is the satisfiability failure the charter demands be surfaced: not
"a delivered Step 6 signature is unsatisfiable" (that would be RED) but
**"the Step 6 grounded forms are satisfiable only on hand-built fibers;
the genuine S1→S5 cascade objects that Piece 2 must supply make the
operative hypotheses (`hfirst`, non-zero `M`) unsatisfiable, because
S1's `goodFiberSet` is empty."** A type-compatibility check passes; a
satisfiability check of the *cascade* does not.

---

## §6. Verdict and recommendation

**Verdict: AMBER.** Part 1: the Step 6 grounded forms are sound and
build clean, the S4 wire is genuine and the S5 G10 wire is genuine, but
the S2 `ε₂` wire is absent, the cascade is uncomposed/parametric, the
witnesses are hand-built, and there are no downstream consumers. Part 2:
S1-E did **not** close the Checkpoint-1 gap (it block-and-reported); the
gap is still open; the ticket body's premise is wrong. The two findings
compound: the cascade looks consumable only because it never touches the
broken S1 output.

**This is a no-go for Piece 2.** Do not dispatch the S7-A-E
concretisation. Dispatching it against the current parametric Step 6
forms would push the unsatisfiability one step downstream — pitfall #6
recurring for the 11th time.

### §6.1. Required before Piece 2 (bounded re-scope, in order)

1. **Re-port the S1-A `IsGoodFiber` G2 clause** — the S1-E §5 forward
   action, unchanged and still gating. A small upstream S1-A-class
   ticket; **needs paper access** (`step1.tex` `def:good-fiber` is not
   in the repo). Acceptance bar: `goodFiberSet a0 a1 ≠ ∅` becomes
   provable — the `interface_part_iv_faithfulness_defect` machine-checked
   refutation flips. Until this lands, every "grounded" cascade output
   downstream is parametric fiction. **This is the same gate that stood
   at Checkpoint 1 and was never cleared.**

2. **Ground G6 and wire S2's `ε₂` into Step 6.** Either ground
   `lem_most_good` (G6) and connect `thm_step2`'s `ε₂` /
   `fiberStaircaseRate` to the Step 6 good/bad split that *produces*
   `badSet` — performing the `ε₂ ↔ C₂'` reconciliation S2-B §2 deferred
   to Checkpoint 2 — or, if `badSet` is to remain a residual parametric
   input by design, document that explicitly and pin the reconciliation
   as a named residual. Currently it is silently absent.

3. **Compose the cascade end-to-end with a genuine-object witness.**
   Replace the free hypotheses of `cascade_steps_1_6_grounded` with the
   actual grounded producers (`lem_sum_step4_grounded` for `hSum`;
   `thm_step5_assembled`'s `Step5Richness` for `hfirst`), and re-do at
   least one concrete witness with an `Fstar` produced by S1's
   `thm_interface` rather than a hand-built singleton — so the
   end-to-end satisfiability is compiler-checked, not asserted.

Items 2 and 3 are genuine Piece-1 completion work; the scoping doc
§2.1's "Piece 1 — Steps 1-6 cascade port" is **not** finished despite
S6-B's "Piece 1 closes". Item 1 is the upstream gate. None is a
re-architecture; the math is sound (mg-8b95 §7).

### §6.2. Doc corrections (done in this commit)

* `OneThird-Option-A-FULL-REFACTOR-scoping.md` §3.3 Checkpoint 2 — the
  AMBER outcome recorded.
* `PROOF-STRUCTURE-ONBOARDING.md` §0 — a Checkpoint-2 bullet added.

---

## §7. Skeptical re-audit of this audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 checklist)

1. **Satisfiability, not a type check.** The verdict does not rest on
   types. Part 2's central claim rests on the in-tree machine-checked
   `goodFiberSet_a0_a1_eq_empty` and on `git log` (no G2 re-port
   commit). Part 1's S2 finding rests on `grep` facts (`ε₂` in zero
   Step 6 files; no `Step6/` file imports `Step2`). The "hand-built
   fibers" finding rests on reading the witness source
   (`pwFstar := fun _ => {gridLinExt}`). The "free parameters / free
   hypotheses" finding rests on reading the *signatures and proof
   bodies* of `thm_step6_grounded` / `cascade_steps_1_6_grounded`, not
   their docstrings.

2. **Discharge-coverage of cited artefacts.** No artefact is
   over-credited. `lem_sum_step4_grounded` is credited as a genuine
   bridge only after reading its body and confirming its output shape
   matches `hSum`. `pair_overlap_sum_ge_vol` is credited only after
   confirming `thm_step6_rich_closure_grounded_of_firstMoment` actually
   invokes it. The "zero consumers" claim is a `grep` over the whole
   tree.

3. **Universal-quantifier truthfulness / not over-blocking.** The audit
   does **not** claim any Step 6 theorem is false — they are true
   parametric theorems, and the verdict is AMBER not RED precisely
   because of that. The S4→S6 wire is credited as genuine. The
   recommended re-scope is bounded and concrete (three items), not a
   re-architecture. The negative claims are each backed by an explicit
   in-tree fact, not asserted.

4. **Did the audit itself fall for "just verify type-compatibility"?**
   No — that is the §6 pitfall the 8th vacuity (mg-faf8) came from. This
   audit explicitly distinguishes type-compatibility (S4 `hSum` shape
   matches; S5 `Step5Richness` shape matches) from satisfiability (§5:
   the genuine S1 objects make `hfirst` / non-zero `M` unsatisfiable).
   The AMBER verdict is driven by the satisfiability failure, not by any
   type mismatch.

---

## §8. Files

* `docs/state-S6-QA-Checkpoint2-Session1.md` — this file (NEW).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` — §3.3 Checkpoint 2
  outcome recorded.
* `docs/PROOF-STRUCTURE-ONBOARDING.md` — §0 Checkpoint-2 bullet.

No Lean source changed — this is an audit.
