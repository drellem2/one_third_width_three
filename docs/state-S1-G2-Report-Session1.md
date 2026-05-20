# State — OneThird S1-G2-Report: re-port `IsGoodFiber`, make `goodFiberSet` non-empty (mg-fc78)

**Ticket:** mg-fc78 — OneThird-S1-G2-Report: re-port the `IsGoodFiber`
G2 clause to genuine order-convexity, make `goodFiberSet` non-empty
provable, complete the S1 corollary upgrades.
**Phase:** FULL REFACTOR Phase 2 — Checkpoint-2 follow-on, item 1 of 3.
The **HARD GATE** for Piece 2.
**Depends:** mg-e996 (S6-QA Checkpoint 2), mg-c2d7 (S1-E), mg-8b95
(Checkpoint 1) — all landed.
**Session:** 1.

---

## §0. Verdict — **GREEN on the hard gate; part 3 block-and-reported**

> **The hard gate is delivered.** `goodFiberSet a0 a1` is now
> **provably non-empty** — in fact `= Finset.univ` — on the concrete
> width-3 non-chain poset `Antichain3`, machine-checked, sorry-free,
> axiom-free (`interface_part_iv_goodFiber_nonempty`,
> `Step1/Interface.lean` §6).  This is the exact flip of the S1-E
> refutation `interface_part_iv_faithfulness_defect`.  The re-port is a
> **genuine** consequence of the corrected `def:good-fiber`, not a
> degenerate re-definition: the good fiber's coordinate image is the
> honest 2-dimensional square `{0,1}²`, and G1/G2/G3 are each verified.
>
> **The S1-E diagnosis was half right — corrected here with paper
> access.** S1-E (mg-c2d7), working *without* `step1.tex`, concluded
> "G2 = rectangle-convexity is too strong".  Reading the paper
> `def:good-fiber` (`step1.tex:114-133`) directly: clause G2 **is**
> literally rectangle-convexity in `ℤ²` — *"`(i,j)` lies in the
> rectangle `[i₀,i₁]×[j₀,j₁]`"*.  G2 is a **faithful** port and is
> **kept unchanged**.  The genuine defect was the **raw fiber**: the
> S1-A port split it by sign (`rawFiber x y L₀ ε`), and a single-sign
> coordinate image lies in the triangle `{i ≤ j}` (resp. `{j ≤ i}`),
> never rectangle-convex for `t ≥ 1`.  The paper's `F_{x,y}(E)` is the
> external-ordering class over **both** signs; G3 needed the diagonal
> sign-flip edge.  See §2.
>
> **Part 3 (corollary upgrades) is block-and-reported as a sub-split.**
> The genuine `|Int_{xy,uv}| = O((t_{xy}+t_{uv})²)` bound for
> `bounded_interaction` requires a faithful port of
> `lem:bounded-interaction`'s strip-counting argument
> (`step1.tex:414-427`), which is a substantial separate formalization
> — the paper proof is itself a sketch ("width-3 bounds the latter by a
> constant per chain position").  Per the ticket's non-triviality bar
> ("not content-free true inequalities") and its "may sub-split"
> clause, `bounded_interaction` is **left as the disclosed-honest
> `|Int| ≤ |𝓛(P)|`** rather than shipping a fake, and the genuine
> `O(t²)` port is recommended as a follow-on (§5).

---

## §1. Scope and method

**Charter (ticket mg-fc78), three parts.**

1. Re-port the `IsGoodFiber` G2 clause to the paper `def:good-fiber`
   order-convexity.
2. **Hard gate:** make `goodFiberSet a0 a1` non-empty **provable** for
   the natural width-3 non-chain pair.
3. Complete the S1 corollary upgrades (`bounded_interaction`,
   `regularOverlap_density`, `regularTripleOverlap_density`,
   `cor:overlap` (b), `cor:triple-overlap` (d)).

**Method.** Paper-first.  `step1.tex` **is** in the repo root (the
earlier S1-E claim that it is not was wrong).  Read `def:good-fiber`
(`step1.tex:114-133`), `thm:interface` part (iii) (`:155-173`,
`:204-246`), the part-(iv) proof (`:300-388`),
`lem:bounded-interaction` (`:397-427`), `cor:overlap` /
`cor:triple-overlap` (`:429-688`), the "Output interface" section
(`:690-731`).  Read every landed S1 Lean file and the S1-E /
Checkpoint-1 / Checkpoint-2 state docs.  Re-port, build, machine-check.

**Build state.** Worktree on `polecat-mg-fc78`.  Mathlib build cache
reused from the source repo (memory note `lean-build-cache-reuse.md`).
`lake build OneThird` clean; the re-ported definitions are sorry-free
and axiom-free.

---

## §2. The genuine defect and the re-port

### §2.1. What `def:good-fiber` actually says

`step1.tex:114-133`.  A **raw fiber** `F_{x,y}(E)` is the
external-ordering class of `E` (`step1.tex:116-120`).  `step1.tex:121`
then partitions `F_{x,y}(E)` *further* by the sign `σ` — but the raw
fiber itself, and its image `D_{x,y}(E) := π_{x,y}(F_{x,y}(E))`, range
over **both** signs.  A raw fiber is **good** if:

* **(G1)** `(i, j, σ)` determines `L` (`cond:G1`);
* **(G2)** `D_{x,y}(E)` is **order-convex in `ℤ²`**, *"meaning if
  `(i₀,j₀),(i₁,j₁)∈D` with `i₀≤i₁` and `j₀≤j₁`, and `(i,j)` lies in the
  rectangle `[i₀,i₁]×[j₀,j₁]`, then `(i,j)∈D`"* (`cond:G2`) — this is
  **literally rectangle-convexity**;
* **(G3)** internal BK edges are exactly the unit grid moves with
  preserved sign **plus the diagonal sign-flip edge at `i = j`**
  (`cond:G3` + part (iii) case (b), `step1.tex:163-166`; Output
  interface, `step1.tex:702`: *"BK edges inside each good raw fiber are
  exactly unit grid moves in `(i,j)`, plus at most one sign-flip edge
  at `i = j`"*).

### §2.2. Why `goodFiberSet` was empty — and why G2 is **not** the bug

S1-E machine-checked `goodFiberSet a0 a1 = ∅` on `Antichain3` and
diagnosed (without paper access) "G2 = rectangle-convexity is too
strong".  The paper shows G2 *is* rectangle-convexity, so a literal
port of G2 is faithful.  The real defect:

* The S1-A `rawFiber x y L₀ ε` was **single-sign** (filtered by
  `signMarker = ε`).
* For sign `+`, `signMarker = true` forces `i(L) ≤ j(L)`
  (`iCoord_le_jCoord_of_sign_true`): a single-sign image lies in the
  **triangle** `{i ≤ j}`.  A triangle is **never** rectangle-convex
  for `t ≥ 1` — `(0,0)` and `(1,1)` in it force `(1,0)`, which violates
  `i ≤ j`.  So G2 rejected every single-sign 2-D fiber.
* The paper's `F_{x,y}(E)` is **both signs**: the `+`-triangle
  `{i ≤ j}` and the `−`-triangle `{j ≤ i}` glued along the diagonal
  give a genuine **rectangle**, which *is* order-convex for a good
  external class.

So the defect was the single-sign `rawFiber`, not G2.  S1-E's verdict
"the good/bad partition is inverted" was correct in effect; its
attribution to G2 was the artefact of not having `step1.tex`.

### §2.3. The re-port (this session)

`lean/OneThird/Step1/LocalCoords.lean`:

* `rawFiber x y L₀` — drop the `ε : Bool` parameter; it is now the
  external-ordering class over both signs
  (`univ.filter (ExternalEquiv x y · L₀)`).
* `IsGoodFiber` G3 — add the sign-flip disjunct: `BKAdj L₁ L₂` iff
  *either* same sign and `±e₁/±e₂` unit move *or* opposite sign with
  `π_{x,y}` unchanged on the diagonal `i = j`.
* **G2 unchanged** — `step1.tex` rectangle-convexity, kept verbatim.
* **G1 unchanged** — `(localCoord, signMarker)`-injective, faithful.
* `goodFiberSet` — redefined over the both-sign `rawFiber`.
* New API: `rawFiber_eq_of_externalEquiv`, `mem_goodFiberSet`,
  `mem_goodFiberSet_of_isGoodFiber`, `IsGoodFiber.card_le_two_sq`
  (a both-sign good raw fiber has `≤ 2·(t+1)²` elements).
* Removed: `signMarker_of_mem_rawFiber` (false — sign is not constant
  on a both-sign raw fiber), `IsGoodFiber.rawFiber_card_le` (the
  single-sign specialisation).

Consumers updated: `GroundSet.lean` (`goodFiber_bkGraph_adj_iff`, the
biUnion forms), `Interface.lean` (`InterfaceConclusion` part (ii)),
`Step2/PerFiberGrounded.lean` (three G3-usage sites — the new sign-flip
disjunct is ruled out by the constant sign of the Step-2 per-fiber
`F`).

---

## §3. The hard gate — `goodFiberSet` is genuinely non-empty

`Step1/Interface.lean` §6.  On `Antichain3` (the 3-element antichain,
the very poset S1-E used to refute non-emptiness) with the rich pair
`(a0, a1)`, `t = 1`:

* there are no external elements, so the external-ordering equivalence
  is total — a **single** raw fiber, all of `𝓛(Antichain3)` (the 6
  linear extensions);
* `isGoodFiber_univ` verifies G1, G2, G3 on that fiber:
  - **G1** — the six extensions carry six distinct `(i, j, σ)`;
  - **G2** — the coordinate image is the full `2×2` square `{0,1}²`,
    which *is* rectangle-convex (every point of any sub-rectangle has
    both coordinates `≤ 1`, hence lies in `{0,1}²`);
  - **G3** — discharged by `decide` over the 36 ordered pairs, with BK
    adjacency made decidable via `bkAdj_iff_posSwap` (a clean
    existential restatement of `BKAdj`);
* `goodFiberSet a0 a1 = Finset.univ`, hence **non-empty**;
* `badSet a0 a1 = ∅`.

`interface_part_iv_goodFiber_nonempty` is the bundled headline — the
exact flip of S1-E's `interface_part_iv_faithfulness_defect`.  No
`sorry`, no `axiom`.

**Non-triviality.** The good fiber is genuine, not degenerate: its
coordinate image is the honest 2-dimensional `{0,1}²` square, not a
collinear strip.  G2 remains the genuine discriminator — a *bad*
external class (one with a Case-3 conflict) has a hole in its
coordinate image and still fails rectangle-convexity.  The non-empty
result is a real proved consequence of the corrected `def:good-fiber`,
exactly as the ticket's non-triviality bar requires.

---

## §4. Part 3 — corollary upgrades: block-and-report

The ticket's part 3 asks for the **genuine quantitative**
`bounded_interaction` (`|Int_{xy,uv}| = O((t_{xy}+t_{uv})²)`) and the
informative density corollaries.  S1-E could not do them because
`goodFiberSet`/`overlap` were empty — that blocker is **removed** by
this session.  But the genuine `O(t²)` bound is *not* unblocked by
non-emptiness alone:

* `bounded_interaction`'s genuine form is `lem:bounded-interaction`
  (`step1.tex:397-427`).  Its proof confines the interaction locus to
  `O(1)` strips, each a union of `O(t)` raw fibers of size `O(t)`.
* That argument is the part-(iv) strip-decomposition machinery.  The
  Checkpoint-1 audit (mg-8b95 §4) and S1-E (§4) both found it **not in
  tree**; only `incompLocus_ordConvex`, `card_externalFinset`,
  `collinear_fiber_card_le` exist.
* The paper proof of `lem:bounded-interaction` is itself a **sketch**
  ("Width-3 bounds the latter by a constant per chain position.
  Summing across the at most 2 rôles ...") — formalising it faithfully
  is a genuine multi-hundred-k undertaking with real risk of surfacing
  an 11th paper-side gap.

Per the ticket's non-triviality bar — *"the corollary bounds must be
the genuine quantitative bounds downstream consumes, not content-free
true inequalities"* — and its explicit "may sub-split" clause:

* `bounded_interaction` is **left as the disclosed-honest
  `|Int| ≤ |𝓛(P)|`**.  Shipping a conditional or fake `O(t²)` would be
  `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #6 recurring.
* `regularOverlap_density` / `regularTripleOverlap_density` are kept —
  they are **genuine set-theoretic containments** (`|Ω∖Ω°| ≤ |Int|`
  etc.), already non-vacuous *as containments*; they become the
  headline `(1−o(1))` density only once `bounded_interaction` is
  genuine.
* The `Corollaries.lean` `AMENDED` banner is updated to the corrected
  diagnosis: the S1-E "empty `goodFiberSet`" blocker is removed; what
  remains is the `lem:bounded-interaction` strip-counting port.

**Recommendation (§5):** file a follow-on for the genuine
`bounded_interaction` `O(t²)` strip-counting port (and the part-(iv)
bad-set cardinality bound it shares machinery with).

---

## §5. Forward action

1. **Hard gate cleared.** `goodFiberSet` non-emptiness is provable;
   Piece 2 is no longer gated by an empty good-fiber set.  The S6-QA
   Checkpoint-2 finding "all grounded cascade output downstream is
   fiction" no longer holds at the definition layer.
2. **Sub-split follow-on (recommended): S1-G2-Report item 3** — the
   genuine `lem:bounded-interaction` `O((t_{xy}+t_{uv})²)` strip port:
   port the part-(iv) bad-set strip decomposition (`step1.tex:300-388`)
   and `lem:bounded-interaction` (`:414-427`); upgrade
   `bounded_interaction`; make the density corollaries headline; deliver
   `cor:overlap` (b) and `cor:triple-overlap` (d).  Budget ~400-700k;
   **paper-rigour risk** — the `lem:bounded-interaction` proof is a
   sketch, audit the strip count for an 11th vacuity before porting.
3. **Checkpoint-2 items 2 and 3** (the other two of the
   checkpoint-2-followon) are unaffected and may proceed.

---

## §6. Skeptical re-audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2)

1. **Satisfiability, not a type check.** The hard gate rests on a
   machine-checked Lean theorem (`interface_part_iv_goodFiber_nonempty`,
   no `sorry`/`axiom`): `goodFiberSet a0 a1 = Finset.univ` is *proved*,
   not asserted.  G1/G2/G3 are each genuinely verified on the concrete
   6-element fiber.
2. **Not a degenerate re-definition.** G2 is kept verbatim as the paper
   rectangle-convexity — the *strongest* faithful reading — so the
   non-emptiness is not bought by weakening the predicate.  The fix is
   to the *raw fiber* (single-sign → both-sign), which is what the
   paper says.  The good fiber's image is genuinely 2-dimensional.
3. **Discharge-coverage.** The part-3 block-and-report is honest: the
   `lem:bounded-interaction` strip machinery is verified **absent** by
   `grep` (pitfall #4), and the paper proof is verified to be a sketch.
   No vacuous `bounded_interaction` is shipped.
4. **Universal-quantifier truthfulness.** The re-port does not over-claim
   `goodFiberSet` is non-empty for *all* rich pairs — it proves it for
   the concrete `Antichain3 (a0, a1)`, the natural minimal width-3
   non-chain witness and the exact poset of the S1-E refutation.

---

## §7. Files

* `lean/OneThird/Step1/LocalCoords.lean` — `rawFiber` re-ported to the
  both-sign external class; `IsGoodFiber` G3 + sign-flip disjunct (G2
  kept); `goodFiberSet` redefined; new API.
* `lean/OneThird/Step1/GroundSet.lean` — `goodFiber_bkGraph_adj_iff`
  and the raw-fiber biUnion forms updated.
* `lean/OneThird/Step1/Interface.lean` — `InterfaceConclusion` part
  (ii) updated; §6 rewritten from the S1-E refutation to the
  non-emptiness proof (`bkAdj_iff_posSwap`, `isGoodFiber_univ`,
  `card_linExt`, `univ_eq_six`, `goodFiberSet_a0_a1_eq_univ`,
  `interface_part_iv_goodFiber_nonempty`).
* `lean/OneThird/Step2/PerFiberGrounded.lean` — three G3-usage sites
  patched for the sign-flip disjunct.
* `lean/OneThird/Step1/Corollaries.lean` — `AMENDED` banner updated to
  the corrected diagnosis (§4).
* `docs/state-S1-G2-Report-Session1.md` — this file (NEW).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` — §0 + §3 pitfall #8 updated.
