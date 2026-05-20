# State — OneThird S1-E: close the Checkpoint-1 AMBER gap (mg-c2d7)

**Ticket:** mg-c2d7 — OneThird-S1-E: close the Checkpoint-1 AMBER gap —
assemble the part-(iv) bad-set cardinality bound, replace the vacuous
Corollaries scaffolds.
**Phase:** FULL REFACTOR Phase 2, S1-E — the bounded follow-on closing
the Checkpoint-1 AMBER gap (the mg-8b95 audit).
**Depends:** mg-8b95 (Checkpoint-1 audit — landed), mg-794c / mg-2e24 /
mg-30e3 / mg-bcf2 (the S1-A/B/C/D ports — landed).
**Session:** 1.

---

## §0. Verdict — **RED (block-and-report): the Checkpoint-1 AMBER gap is a definition-layer bug, not an assembly gap**

> The Checkpoint-1 audit (mg-8b95) scoped S1-E as an **assembly-only**
> follow-on: per its §8.1, "the strip count and
> `collinear_fiber_card_le` are in tree — what is missing is the
> *assembly* into a cardinality statement." Executing S1-E refutes that
> framing on **two** counts:
>
> 1. **The strip-count machinery is NOT in tree.** Only
>    `incompLocus_ordConvex`, `card_externalFinset` and
>    `collinear_fiber_card_le` are in tree (BadSet.lean). There is no
>    decomposition of `badSet` into strips, no count of bad raw fibers,
>    and no proof that bad raw fibers are collinear. The audit's "strip
>    count … in tree" claim does not survive a `grep`
>    (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #4).
>
> 2. **More fundamentally — and this is the load-bearing finding — the
>    bad-set bound CANNOT be assembled on top of the landed
>    definitions at all**, because the S1-A `IsGoodFiber`
>    order-convexity clause (G2, `LocalCoords.lean:209-214`) is **too
>    strong**. It demands the coordinate image be *rectangle*-convex in
>    `ℕ²`, but a genuine constant-sign raw fiber's image is a
>    *triangle* (`signMarker = true` forces `iCoord ≤ jCoord`), never a
>    rectangle for `t ≥ 1`. The consequence is **inversion**: the
>    landed `goodFiberSet` is degenerate (empty for every pair with
>    `t ≥ 1`) and `badSet` is the bulk. The operative part-(iv) content
>    `|Bad_{x,y}| ≪ |F_{x,y}|` is not *undelivered* — under the landed
>    definition it is **false**.

**This is a fresh vacuity/faithfulness discovery** — the 10th of the
OneThird arc (after mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970,
mg-ac13, mg-5fbd, mg-0bd1, mg-fdc2). It is a *definition-layer* bug:
the proposition the paper proves is sound (the audit mg-8b95 §7 verified
the paper math), but the Lean port of `def:good-fiber` does not capture
it. The mg-8b95 audit itself missed this — it focused on the
`|I(z)| ≤ 2` imprecision and the "undelivered assembly", and never
checked whether `goodFiberSet` is non-empty (its Finding 3 noted part
(ii) is "tautological" but did not compute `goodFiberSet`).

**Severity = RED for the S1-E assembly-only scope; the overall proof is
not dead.** Re-porting one clause of one S1-A definition unblocks the
assembly. But S1-E as scoped — "assemble + replace the scaffolds" with
the file scope `Interface.lean` / `Corollaries.lean` — cannot be
completed, because the fix is in `LocalCoords.lean` (S1-A), outside the
S1-E file scope, and no genuine bound can be assembled before it.

**Delivered this session (genuine, machine-checked):**

* A full Lean **machine-checked refutation** in `Interface.lean` §6 —
  `interface_part_iv_faithfulness_defect`: at the concrete width-3
  non-chain poset `Antichain3`, **every** raw fiber of the rich pair
  `(a0, a1)` is rejected by G2, so `goodFiberSet a0 a1 = ∅` and
  `badSet a0 a1 = 𝓛(P)`. No `sorry`, no `axiom`.
* The supporting general lemmas `iCoord_le_jCoord_of_sign_true`,
  `jCoord_le_iCoord_of_sign_false` (the triangle constraint),
  `goodFiber_image_no_unit_square` / `_no_unit_square'` (the precise
  G2 defect: a good constant-sign fiber's image cannot contain both
  `(0,0)` and `(1,1)`), `rawFiber_eq_of_externalEquiv`,
  `mem_goodFiberSet` — sound, general, reusable once G2 is fixed.
* An `AMENDED` banner in `Corollaries.lean` recording why the vacuous
  `bounded_interaction` / `regularOverlap_density` /
  `regularTripleOverlap_density` scaffolds are **left as-is** (a
  conditional upgrade would be a fresh content-free scaffold).
* This state document + onboarding pitfall #8 + Checkpoint-1 §11.

**Not delivered (blocked, per the non-triviality bar):** the
quantitative `|Bad_{x,y}| = O(|Z|·t²)` bound, the genuine
`bounded_interaction` upgrade, `cor:overlap` (b), `cor:triple-overlap`
(d), and the rich-regime negligibility. All of them are consumers of
`goodFiberSet` / `badSet` / `overlap`, which are degenerate under the
current `IsGoodFiber`. Delivering them now — even in threaded-hypothesis
form — would ship signatures whose structural hypotheses are
unsatisfiable on the current definitions: pitfall #6 (the 8th vacuity)
exactly. The ticket's non-triviality bar mandates block-and-report
instead.

---

## §1. Scope and method

**Charter (ticket mg-c2d7).** Four items (mg-8b95 audit §8.1):
(1) assemble the part-(iv) bad-set cardinality bound in the corrected
`|Bad_{x,y}| = O(|Z|·t²)` form; (2) replace the vacuous
`Corollaries.lean` scaffolds (`bounded_interaction`,
`regularOverlap_density`, `regularTripleOverlap_density`) and deliver
`cor:overlap` (b) / `cor:triple-overlap` (d); (3) thread the
rich-regime richness hypothesis explicitly; (4) decide the
`goodFiberSet` non-emptiness wiring. Lean file scope:
`Step1/Interface.lean`, `Step1/Corollaries.lean`. **Non-triviality
bar:** a true-but-content-free bound is vacuous even if it type-checks;
deliver the genuine quantitative bound or **block-and-report**.

**Method.** Paper-and-code reading + Lean. Read every landed S1 file
(`LocalCoords.lean`, `BadSet.lean`, `Corollaries.lean`,
`Interface.lean`, `GroundSet.lean`, `BKMoves.lean`, `Overlap.lean`) and
the Checkpoint-1 audit. Verified the "in tree" claims of audit §8.1 by
`grep` (pitfall #4). Built a concrete worked refutation on `Antichain3`
and **machine-checked it in Lean** — §3.

**Build state.** Worktree on `polecat-c2d7` off `7feef5c`.
`lake build OneThird.Step1.Interface` clean (the mathlib build cache
was reused from the source repo per the memory note
`lean-build-cache-reuse.md`). No `sorry`, no `axiom` added.

---

## §2. The defect — `IsGoodFiber` G2 is rectangle-convexity, which is too strong

### §2.1. What G2 says

`IsGoodFiber x y F` (`LocalCoords.lean:204-225`) is a conjunction of
three clauses. Clause **G2** (`:209-214`):

```
∀ p ∈ F.image (localCoord x y), ∀ q ∈ F.image (localCoord x y),
  p.1 ≤ q.1 → p.2 ≤ q.2 →
  ∀ r : ℕ × ℕ, (p.1 ≤ r.1 ∧ r.1 ≤ q.1) → (p.2 ≤ r.2 ∧ r.2 ≤ q.2) →
    r ∈ F.image (localCoord x y)
```

This says: for any two image points `p ≤ q` (componentwise), the
**entire axis-aligned rectangle** `[p.1,q.1] × [p.2,q.2]` lies in the
image. This is *rectangle-convexity* for the product order on `ℕ²`.

### §2.2. Why a genuine fiber can never satisfy it

A raw fiber `rawFiber x y L₀ ε` (`LocalCoords.lean:153-158`) is the
**full** external-equivalence class at sign `ε` — every linear
extension externally equivalent to `L₀` with `signMarker = ε`.

On such a fiber the sign is constant. For sign `+` (`signMarker = true`,
i.e. `x <_L y`): every common neighbour preceding `x` also precedes
`y`, so

> `iCoord x y L ≤ jCoord x y L` for every `L` in the fiber.

(Machine-checked: `iCoord_le_jCoord_of_sign_true`, `Interface.lean` §6.
Mirror for sign `−`: `jCoord_le_iCoord_of_sign_false`.)

So a sign-`+` fiber's coordinate image lies inside the **triangle**
`{(i,j) : i ≤ j}`. A triangle is **not** a rectangle for `t ≥ 1`: if
the image contains `(0,0)` and `(1,1)`, rectangle-convexity forces
`(1,0)` into the image — but `(1,0)` violates `i ≤ j`. Hence:

> **`goodFiber_image_no_unit_square`** (machine-checked,
> `Interface.lean` §6): a good fiber on which the sign is constantly
> `+` cannot have both `(0,0)` and `(1,1)` in its coordinate image.

Equivalently: G2 rejects every genuine two-dimensional sign-`+` fiber.
The only fibers G2 accepts are those whose image is *itself* a
rectangle — and inside the triangle `{i ≤ j}` the only rectangles are
degenerate (a single row, a single column, or a point). So a "good"
fiber under the landed G2 is forced to be **collinear or a point** —
exactly the shape the paper calls *bad*. **The good/bad classification
is inverted.**

### §2.3. The paper's `def:good-fiber` G2 is a different notion

The paper's part (iv) asserts `Bad_{x,y}` is "one-dimensional"
(collinear) and `F_{x,y}` is the factorial-scale bulk (mg-8b95 §7).
Both are impossible if G2 = rectangle-convexity (which makes the
collinear fibers *good* and the 2-D fibers *bad*). So the paper's G2
("the coordinate image is order-convex") must mean order-convexity
*along the realised staircase / BK-move graph*, not product-order
rectangle-convexity. The S1-A port (mg-30e3, `LocalCoords.lean`) chose
the literal product-order reading, and it is wrong. Re-porting this one
clause is the fix (§5).

---

## §3. The machine-checked refutation (`Interface.lean` §6)

The finding is not argued in prose alone — it is a Lean theorem with no
`sorry` and no `axiom`. The witness is `Antichain3`, the 3-element
antichain (the very poset the S1-A/S1-D non-vacuity witnesses
`localInterface_nonvacuous` / `thm_interface_nonvacuous` use), with the
rich pair `(a0, a1)`, `t(a0,a1) = 1`.

* **Four explicit linear extensions** are constructed via
  `linExtOfEquiv` and concrete `Fin 3` permutations: `extId`
  (`a0<a1<a2`, sign `+`, coord `(0,0)`), `extCyc` (`a2<a0<a1`, sign
  `+`, coord `(1,1)`), `extSwap` (`a1<a0<a2`, sign `−`, coord
  `(0,0)`), `extRev` (`a2<a1<a0`, sign `−`, coord `(1,1)`). Their
  signs and local coordinates are computed and proved
  (`sign_extId … localCoord_extRev`).
* `externalEquiv_total`: on `Antichain3` there are no external
  elements, so `ExternalEquiv a0 a1` relates every pair — one external
  class, refined only by sign.
* **`not_isGoodFiber_plus`**: the sign-`+` raw fiber contains `extId`
  (coord `(0,0)`) and `extCyc` (coord `(1,1)`); by
  `goodFiber_image_no_unit_square`, G2 fails — the fiber is bad.
* **`not_isGoodFiber_minus`**: the symmetric statement for the sign-`−`
  raw fiber (via `goodFiber_image_no_unit_square'`).
* **`goodFiberSet_a0_a1_eq_empty`**: every linear extension's raw fiber
  is one of those two (one external class × two signs), both bad — so
  `goodFiberSet a0 a1 = ∅`.
* **`badSet_a0_a1_eq_univ`**: hence `badSet a0 a1 = 𝓛(P)`.
* **`interface_part_iv_faithfulness_defect`**: the bundled headline.

So at a concrete, genuine, width-3 non-chain poset, the interface
theorem's good-fiber set — the object the entire part-(ii)/part-(iv)
machinery is *about* — is **empty**, and the bad set is **all** of
`𝓛(P)`. The audit's degenerate-witness warning (mg-8b95 §0: "the
witnesses are degenerate") is now precise and machine-checked: the
non-vacuity witnesses `localInterface_nonvacuous` /
`thm_interface_nonvacuous` only ever assert the *tautological* part-(ii)
partition (`goodFiberSet ∪ badSet = univ`, true for any partition of
`univ`), and never that `goodFiberSet` is non-empty — which it is not.

---

## §4. Why each S1-E item is blocked

| Item | What it needs | Status |
|---|---|---|
| **1. `|Bad| = O(|Z|·t²)`** | `badSet` = union of *collinear* bad raw fibers, count `O(|Z|·t)` | **BLOCKED.** Bad raw fibers are 2-D triangles, not collinear; `collinear_fiber_card_le`'s `hline` hypothesis is unsatisfiable for them. Even the per-fiber `(t+1)²` bound needs G1-injectivity, which is not automatic (the `rawFiber` definition does not pin `x`/`y` vs. external order). And `badSet` itself is the wrong object (it is `𝓛(P)`, not the negligible set). |
| **2. `bounded_interaction` upgrade** | `|Int| = O((t_{xy}+t_{uv})²)` on `Ω = goodFiberSet x y ∩ goodFiberSet u v` | **BLOCKED.** `Ω` is empty for any rich pair (`t ≥ 1`), so a genuine `O(t²)` bound is unobtainable; a conditional one would have an unsatisfiable hypothesis (pitfall #6). The vacuous `|Int| ≤ |𝓛(P)|` is **left as-is** with a disclosure banner. |
| **3. Thread richness** | `|F_{x,y}| ≥ c·n²` (or `\|Z\|!`-class) ⇒ `|Bad| ≪ |F|` | **BLOCKED & vacuous.** `|F_{x,y}| = |goodFiberSet x y| = 0` for `t ≥ 1`, so any richness lower bound is *false*, not merely a documented hypothesis. Threading it would be threading `False`. |
| **4. `goodFiberSet` non-emptiness** | a proved `goodFiberSet x y ≠ ∅` | **BLOCKED — the opposite is true.** `goodFiberSet_a0_a1_eq_empty` proves `goodFiberSet a0 a1 = ∅`. Non-emptiness is *false* under the current `IsGoodFiber`. |

Every item is a consumer of `goodFiberSet` / `badSet` / `overlap`, all
degenerate under the broken G2. None can be delivered in genuine form
until G2 is fixed. Per the non-triviality bar, S1-E ships none of them.

---

## §5. Forward action — what actually closes the Checkpoint-1 gap

The Checkpoint-1 AMBER gap is real, but its remedy is **not** an
assembly ticket. The required work, in order:

1. **Re-port the S1-A `IsGoodFiber` G2 clause** (`LocalCoords.lean`,
   work item mg-30e3 territory — a *new* S1-A-class ticket, **not**
   S1-E). Replace product-order rectangle-convexity with the paper's
   genuine `def:good-fiber` order-convexity (staircase / BK-move-graph
   convexity). This must be done against the paper `step1.tex`
   `def:good-fiber` — the paper text is **not in this repo**, so the
   re-port ticket must be dispatched with paper access. Acceptance bar:
   `goodFiberSet a0 a1 ≠ ∅` becomes provable (the §3 machine-checked
   refutation flips). Likely also revisit `rawFiber` /
   `IsGoodFiber.card_le_sq` (which assumes the rectangle image) and the
   G1-injectivity automaticity (not currently proved; see §4 item 1).
2. **Then** re-scope an S1-E' assembly ticket against the corrected
   definitions: the bad-set cardinality bound, the `bounded_interaction`
   upgrade, the density corollaries, the richness threading. With a
   correct `IsGoodFiber`, the threaded-hypothesis pattern the audit
   §8.1 item 3 prescribes becomes genuine (satisfiable hypotheses).
3. **Re-audit the S1-A acceptance witnesses.**
   `localInterface_nonvacuous` (`GroundSet.lean`) and
   `thm_interface_nonvacuous` (`Interface.lean`) advertise non-vacuity
   but only check the tautological part-(ii) partition. After the G2
   re-port they should additionally assert `goodFiberSet ≠ ∅`.

This is **not** in the S1-E budget or file scope and is recorded here
as the forward recommendation. It is a small ticket (one definition
clause + its immediate API), but it is upstream and gating.

**Checkpoint-1 / Wave-4 consequence.** mg-8b95 §8.3 already gated Step 6
cascade assembly behind S1-E. That gate **stands and tightens**: the
gating prerequisite is now the G2 re-port, not an assembly. Step 6
individual grounded lemmas may still be ported hypothesis-first; the
cascade assembly remains blocked.

---

## §6. Skeptical re-audit of this finding (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 checklist)

1. **Satisfiability / not a type check.** The verdict rests on a
   machine-checked Lean theorem (`interface_part_iv_faithfulness_defect`,
   no `sorry`/`axiom`), not on reasoning. `goodFiberSet a0 a1 = ∅` is
   proved, not asserted.
2. **Discharge-coverage.** The audit mg-8b95 §8.1 claim "the strip
   count … in tree" was checked by `grep` and is false (pitfall #4):
   no strip decomposition, count, or bad-fiber-collinearity lemma
   exists. Only `incompLocus_ordConvex`, `card_externalFinset`,
   `collinear_fiber_card_le` are in tree.
3. **Universal-quantifier truthfulness.** The central negative claim
   ("the `O(|Z|·t²)` bound is not assemblable") is backed by an
   explicit concrete refutation (`Antichain3`), and the mechanism
   (`signMarker = + ⇒ i ≤ j`, triangle ≠ rectangle) is a general lemma,
   so it scales to every `t ≥ 1` pair, not just `Antichain3`.
4. **Not over-blocking.** The block is per-item (§4) and the genuine,
   sound, reusable lemmas (`rawFiber_eq_of_externalEquiv`,
   `mem_goodFiberSet`, the two `goodFiber_image_no_unit_square`, the
   sign/coordinate lemmas) **are** delivered — they survive the G2
   re-port unchanged and are forward-useful.

---

## §7. Files

* `docs/state-S1-E-Session1.md` — this file (NEW).
* `lean/OneThird/Step1/Interface.lean` — §6 added: the machine-checked
  faithfulness-defect section (general lemmas + `Antichain3` witness +
  `interface_part_iv_faithfulness_defect`); module docstring §6 note.
* `lean/OneThird/Step1/Corollaries.lean` — `AMENDED (S1-E)` banner in
  the "Scaffold vs. paper strength" docstring section; no theorem
  changes (the vacuous scaffolds are deliberately left as-is).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` — §3 pitfall #8 (the 10th
  vacuity discovery); §0 bullet.
* `docs/state-S1234-QA-Checkpoint1-Session1.md` — §11 S1-E outcome.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` — §2.1 / §3.3
  note.
