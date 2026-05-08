# Path α — cumulative state

**Owner.** PM (mayor) maintains the doc; future Path-α-flavoured
polecats are required to **read this first** and **update it as part
of their deliverable**.

**Source of truth.** This is the single cumulative state document for
the Path α execution arc. Per
`feedback_polecat_cumulative_state_doc` (2026-05-06): individual
polecat reports remain immutable artefacts (referenced below), but
this doc is what reflects **current** consensus and **current**
open questions.

**Last update.** mg-21a4 (cat-mg-21a4), 2026-05-06. Created.
**Last update.** mg-bb74 (cat-mg-bb74), 2026-05-07. §3.1 closed
(Path γ confirmed); `lean/AXIOMS.md` framing refreshed from
"scheduled for replacement" to "definitively retained" /
"indefinitely deferred."
**Last update.** mg-91be (cat-mg-91be), 2026-05-07. Sub-α-C
scoping in flight (§3.4 added, AMBER leaning GREEN); §1.8 added
(Stanley `μ` log-supermod corollary); §3.5–§3.8 added (Daniel-help
leverage points DH-1 through DH-4); §4.5 added (sub-α-C decision
points and triggers). Per Daniel directive 2026-05-07T16:06Z
(`feedback_long_arcs_are_pm_authority`), PM commits the sub-α-C
long arc; mg-fb16 unhold remains released for Path γ ship velocity.
**Last update.** mg-c7b9 (cat-mg-c7b9), 2026-05-07. EX-1 Session A
scoping done (§1.9 added, variant chosen = Bjorner combinatorial
induction); §3.4 updated (first execution ticket of sub-α-C filed,
EX-1 Session A latex done, **AMBER verdict** with open inductive
closure question); §3.5 (DH-1) refined with the specific upstream
PR target (`Mathlib/Combinatorics/Order/StanleyLogSupermod.lean`,
maintainer Yael Dillies). PM next step: file **Session A.2**
follow-up scoping ticket to close the inductive closure gap (or
survey alternative proof routes) before dispatching Session B.
**Last update.** mg-7928 (cat-mg-7928), 2026-05-07. EX-1 Session
A.2 scoping done (§1.9 updated to mark variant-3 closure RED on
fresh structural fact; §1.10 NEW for the Session A.2 verdict);
§3.4 updated (EX-1 sub-level verdict shifted to "variant-3 RED,
variant-1 viable, Options A–D"); §3.5 (DH-1) leverage heightened
post-A.2; §4.5 updated with Daniel decision point on Options A–D.
PM next step: **mail Daniel** with the four-option PM action item
(Option A: DH-1 + temporary axiom, recommended; Option B:
commit to Variant 1 AF; Option C: Session A.3 literature lookup;
Option D: rescope sub-α-C entirely).
**Last update.** mg-d0fc (cat-mg-d0fc), 2026-05-08. **Option A
executed.** §1.11 NEW for the temp-axiom land
(`OneThird.LinearExt.stanley_log_supermod` in
`lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`);
§3.4 updated (Option A status: executed; sub-α-C arc next
execution ticket = EX-3 chamber-decomposition scoping); §4.5
updated (decision point closed — Option A picked + executed by PM;
DH-1 surface to Daniel pending evening digest). AXIOMS.md gains
a third audit-bar 4-condition entry for the temp axiom; trust
surface for the `width3_one_third_two_thirds` headline is unchanged
(still two named axioms + `native_decide` quintet). The corollary
`stanley_mu_log_supermod` (μ(I) := e(I)·e(α \ I) log-supermod) is
deferred to a narrow follow-up ticket — see §1.11 + AXIOMS.md
"Corollary deferred" — pending either a `numLinExt`-on-dual bridge
lemma or a parallel upper-set axiom. PM next step: file EX-3
scoping ticket.
**Last update.** mg-163f (cat-mg-163f), 2026-05-08. **Path-A-vs-
Path-B fork resolved: GREEN-A.** §1.12 NEW for the fork-resolution
deliverable (`docs/path-alpha-execution-arc/path-A-vs-path-B-fork-
resolution.md`); §3.4 updated (sub-α-C arc-level verdict upgraded
to GREEN; Path A committed; Path B AMBER-leaning-RED at level-`k`
localisation step per §3.4 of the deliverable); §3.9 NEW (DH-4
heightened post-fork-resolution; EX-6 continuous FKG is now the
single largest mathlib-PR-class chunk and the highest-leverage
DH after DH-1); §4.5 updated (fork-resolution decision point
closed; PM commits Path A; EX-3 = next execution ticket; Path A
LoC refined to ~4450–7700 post-EX-1-landing). Sub-α-C arc-level
verdict is now GREEN. Path A's only material RED risk is EX-6
(continuous FKG) which is AMBER with a clean integer-sub-lattice
fallback for fixed-`α` applications. PM next step: file EX-3
scoping ticket; surface DH-4 to Daniel as heightened leverage
point alongside DH-1.
**Last update.** mg-8c66 (cat-mg-8c66), 2026-05-08. **EX-3
executed: `OrderPolytope α` landed.** §1.13 NEW for the EX-3
deliverable (`lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`):
`OrderPolytope α` defined as the set of order-preserving maps
`α → [0,1] ⊆ ℝ`, with named theorems for its convexity
(`OrderPolytope.convex`), closedness (`OrderPolytope.isClosed`),
boundedness (`OrderPolytope.isBounded`), compactness
(`OrderPolytope.isCompact`, requires `[Fintype α]`), and Borel
measurability (`OrderPolytope.measurableSet`, requires
`[Fintype α]`). The discrete-3-antichain hand-verification
(mg-163f §5 / EX-3 brief §2.3) is in tree as a generic lemma
`OrderPolytope.eq_cube_of_discrete` plus an `example` instantiating
it on `Three := {a, b, c}` with the discrete partial order to
witness `O(Three) = [0,1]^Three`. §3.4 updated (sub-α-C arc:
EX-3 done; EX-4 scoping is the next execution ticket). The
`Mathlib.Order.LowerSet.Basic` import sketched in mg-163f §5.3
was renamed to `Mathlib.Order.UpperLower.Basic` in this Mathlib
version (v4.29.1); minor signature-template adjustment, no
mathematical change. Trip-wires not fired: build green; no
mathlib refactor needed; no token blow-up. Trust surface
unchanged (still two named axioms + Stanley temp axiom for sub-α-C).
PM next step: file EX-4 scoping ticket (Stanley vertex theorem).

---

## §1 Verified — what is mathematically established

### §1.1 The drops headline reduces to FKG positive correlation on `LinearExt' Q`

* **Source.** mg-b10a §2 (`docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`,
  commit `256f0da`).
* **Statement.** The single-edge `addRel` induction for
  `probEvent'_mono_of_subseteq_upClosed` reduces to the inequality
  `|A| · |R| ≤ |A ∩ R| · |L(Q)|`, where
  `A = {L : S(L.iI k)}` and `R = {L : a <_L b}`. This is **FKG
  positive correlation between `A` and `R` under uniform `L(Q)`**.
* **Verdict.** Verified. Direction confirmed by hand on a
  3-element example (mg-b10a §2; `α = {a,b,c}`, `Q = discrete`,
  `k = 1`, `S = "{a} ⊆ I"`).

### §1.2 None of the natural lattice candidates on `LinearExt' Q` is distributive

* **Source.** mg-b10a §3.2 (commit `256f0da`); reaffirmed by
  mg-dc9d §2 (commit `a95020e`).
* **Statement.** The five candidates surveyed (Bruhat, weak,
  inversion-set inclusion, chain-of-ideals embedding, Hibi
  chambers) all fail to be distributive lattices on the full
  `LinearExt' Q`. The third row, "inversion-set inclusion (with
  fixed `τ`)" = `(L(α), ≤_τ)` = right weak Bruhat order on
  `S_n` for the discrete-`n` case; `n = 3` is the canonical
  S₃ hexagon non-distributive lattice.
* **Verdict.** Verified. mg-dc9d §2 includes the explicit Hasse
  diagram and the failed distributive law:
  `(U ∨ V) ∧ X = X` while `(U ∧ X) ∨ (V ∧ X) = U`, and `X ≠ U`.

### §1.3 Birkhoff: `LowerSet α` IS a finite distributive lattice

* **Source.** Mathlib (`Mathlib.Order.LowerSet`, `Mathlib.Order.Birkhoff`);
  used in tree at `lean/OneThird/Mathlib/LinearExtension/Birkhoff.lean`.
* **Statement.** For any finite poset `α`, the lattice `LowerSet α`
  of order ideals is finite distributive. Mathlib's `fkg` /
  `four_functions_theorem` apply.
* **Verdict.** Verified, in mathlib.

### §1.4 The product-lattice FKG-on-LE pathway (with lossy factor)

* **Source.** `lean/OneThird/Mathlib/LinearExtension/FKG.lean:452`
  (`fkg_uniform_initialLowerSet`); data version at
  `lean/OneThird/Mathlib/RelationPoset/FKG.lean:325`
  (`fkg_uniform_initialLowerSet'`).
* **Statement.** For monotone non-negative `F, G : LowerSet α → β`
  pulled back along the level-`k` projection,
  `(∑_L F(L_k))(∑_L G(L_k)) ≤ |product| · ∑_ω F(ω_k)·G(ω_k)`,
  where `|product| = |LowerSet α|^{n+1} = (2^{|J(α)|})^{n+1}`
  worst-case.
* **Verdict.** Verified, in tree. Lossy: factor is exponentially
  larger than `numLinExt α`.

### §1.5 Stanley log-supermodularity of `e : J(P) → ℕ`

* **Source.** Stanley, *Two combinatorial applications of the
  Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A, 1981.
* **Statement.** `e(I ∪ J) · e(I ∩ J) ≥ e(I) · e(J)` for all
  `I, J ∈ J(P)`. Hence `μ(I) := e(I) · e(P \ I)` is also
  log-supermodular on `J(P)`.
* **Verdict.** Verified, in literature. **Not in mathlib.** Would
  be in scope for a future mathlib PR if anyone wanted to port it.
* **Use.** Mathematical context only — does not give a level-`k`
  FKG (see §3, mg-21a4).

### §1.6 Sub-α-A is RED (mg-21a4)

* **Source.** mg-21a4 §3 (`docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`,
  this commit).
* **Statement.** Per-level FKG between two level-`k` pullback events
  under uniform `L(α)` measure is **false in general**. Concrete
  counterexample on the discrete 3-antichain at `k = 1`:
  `Pr[a ∈ L_1 ∧ b ∈ L_1] = 0 < 1/9 = Pr[a ∈ L_1] · Pr[b ∈ L_1]`.
  Negative correlation.
* **Verdict.** Verified by counterexample. Sub-α-A's mitigation
  hypothesis (mg-dc9d §6.1) does not exist.

### §1.7 The drops application requires global (non-level) `R`

* **Source.** mg-21a4 §3.3.
* **Statement.** The single-edge inductive step's `R = {L : a <_L b}`
  is not a level-`k` pullback of any monotone event on `Finset α`,
  for any `k`. So even if a per-level FKG existed (it doesn't), it
  could not bound `Pr[A ∩ R]` for the drops headline.
* **Verdict.** Verified. Together with §1.6, this is the doubly-RED
  obstruction on sub-α-A.

### §1.8 `μ(I) := e(I) · e(α \ I)` is log-supermodular on `J(α)`

* **Source.** mg-91be §3.2 (sub-α-C scoping); originally Stanley
  1981.
* **Statement.** For `μ : J(α) → ℕ` defined by `μ(I) := e(I) ·
  e(α \ I)` (where `e(K) = |L(α[K])|`), `μ` is log-supermodular on
  `J(α)`: `μ(I) μ(J) ≤ μ(I ∪ J) μ(I ∩ J)`. Follows from §1.5
  (Stanley log-supermod of `e` on both `J(α)` and the dual) and
  De Morgan's law.
* **Verdict.** Verified, in literature; not in mathlib. Caveat:
  `μ` is supported on **all of `J(α)`** (sums over levels); the
  level-`k` restriction of `μ` is **not** log-supermodular per
  mg-21a4 §3.2 (size-mismatch failure). This is why the chamber
  decomposition (geometric level-`k` localisation via the
  hyperplane slice `t_(k) = const` of the cube `[0,1]^α`) is
  essential to sub-α-C.

### §1.9 EX-1 (Stanley log-supermod) — variant-3 closure RED; variant-1 (AF) viable

* **Source.** mg-c7b9 (variant-3 chosen);
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-scoping.md`.
  Updated by mg-7928 (variant-3 closure RED'd; variant-1 surfaced);
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-induction-closure.md`.
* **Statement.** Of the four candidate proof variants for Stanley
  log-supermodularity (Stanley 1981 AF; Daykin 1990 4FT-direct;
  Bjorner 1989 combinatorial induction; fresh combinatorial):
  - **Variant 3 (Bjorner combinatorial induction)** was chosen by
    mg-c7b9 as the most upstream-PR-class option, but its
    inductive closure is **RED on a fresh structural fact**
    (mg-7928 §1.2): the Bjorner injection
    `Ψ : LE(α[I]) × LE(α[J]) ↪ LE(α[I⁺]) × LE(α[J⁺])` combined
    with the IH on the smaller-δ pair produces the inequality
    `e(I) e(J) ≤ e(I ∪ J) · e((I ∩ J) ∪ {m, m'})`, which is
    **strictly weaker** than the target
    `e(I) e(J) ≤ e(I ∪ J) · e(I ∩ J)` because `e(·)` is monotone
    increasing in `K` (so `e((I ∩ J) ∪ {m, m'}) ≥ e(I ∩ J)`).
    No IH re-application closes the gap (mg-7928 §1.3 enumerates
    candidate sub-pairs and rules each out).
  - **Variant 2 (4FT-direct)** REJECT (reaffirmed): 4FT consumes
    log-supermodularity as hypothesis, doesn't produce it.
  - **Variant 4 (fresh)** REJECT: Stanley log-supermod is
    genuinely deep; a fresh proof would constitute new mathematics
    out of polecat scope.
  - **Variant 1 (Stanley 1981 Aleksandrov–Fenchel)** is the only
    literature-known viable route. Heavy mathlib gap (~3000–5000
    LoC for AF inequality + order polytope volume formulas
    + mixed volume infrastructure), partially amortised against
    sub-α-C Path A's chamber decomp arc.
* **Verdict (mg-7928 Session A.2).** **AMBER, variant-3 RED.**
  Variant-3 closure cannot be made rigorous within the Bjorner
  framework. Variant-1 is heavy but viable. **Four PM action
  options surfaced** (mg-7928 §3.1): Option A (DH-1 + temporary
  axiom, recommended), Option B (commit to Variant 1 AF),
  Option C (Session A.3 literature lookup), Option D (rescope
  sub-α-C entirely — Daniel's authority). PM mails Daniel with
  the four options.

### §1.12 Path-A-vs-Path-B fork resolved — GREEN-A; PM commits Path A

* **Source.** mg-163f (this update);
  `docs/path-alpha-execution-arc/path-A-vs-path-B-fork-resolution.md`.
* **Statement.** Per mg-91be §4.3 / state.md §3.4 hand-off, the
  Path-A-vs-Path-B fork was filed for re-evaluation post-EX-1-
  landing. mg-163f's scoping resolves the fork: **Path B's
  level-`k` localisation step is AMBER-leaning-RED.** The four
  candidate sub-formulations (B-1) restrict-to-level-`k`, (B-2)
  tilted-measure, (B-3) level-decorated lattice, and (B-4)
  direct-injection — all hit structural obstructions of the same
  character as the mg-21a4 §3.2 size-mismatch class. (B-3) was
  newly resolved in this scoping: under product order on
  `J(α) × Fin (n+1)`, the level-decorated Holley either degenerates
  (level-locked indicator `1[|I| = k]` exits its support under
  lattice ops) or factorises to the un-decorated Holley with no
  level-`k` content gained. (B-4) was newly resolved: the
  generating-function attack on the tilted measure gives only
  `(0, ∞)`-pointwise polynomial inequalities, which do not imply
  per-coefficient inequalities (counterexample: `g(z) = (z-1)^2 ≥ 0`
  on ℝ but with negative middle coefficient).
* **Path A LoC refinement post-EX-1-landing.** Aggregate
  ~4450–7700 LoC (down from sub-α-C scoping §5.11's 5050–8700 by
  ~600–1000 LoC: EX-1 collapses to 0 as axiom; EX-5 drops by
  ~50–200 LoC because the Stanley axiom collapses sub-poset volume
  identity to a 1-line invocation). Within ~1.15× of state.md §4.2
  working figure (3450–6700 LoC).
* **Path A material RED risks.** Single risk: EX-6 (continuous
  FKG/AD on `[0,1]^n`) is AMBER. mg-163f §2.3 surveyed mathlib
  prerequisites (`Mathlib.MeasureTheory`, `four_functions_theorem`,
  `Mathlib.Analysis.Convex.Basic`) and finds **no structural
  obstacle**; the standard Riemann-sum discretisation route is
  Lean-portable. Fallback: integer-sub-lattice discretisation gives
  weaker drops with size-`N` factor; for fixed-`α` applications
  (case3, Brightwell), factor is constant, so applications still
  close. Path A does **not** structurally collapse under EX-6 RED.
* **Verdict.** **GREEN-A.** PM commits Path A. EX-3 (order polytope
  `O(α)` as Lean type) is the next execution ticket; spec drafted
  in mg-163f §5: ~300–500 LoC, ~200–300k tokens, 1 polecat
  session.

### §1.13 EX-3 executed — `OrderPolytope α` landed with basic instances

* **Source.** mg-8c66 (this update);
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`.
* **Statement.** The order polytope `O(α)` of a finite poset `α`
  is defined as

  ```lean
  def OrderPolytope (α : Type*) [PartialOrder α] : Set (α → ℝ) :=
    { f : α → ℝ |
        (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ x y, x ≤ y → f x ≤ f y) }
  ```

  in the `OneThird.LinearExt` namespace. Five named theorems
  populate the basic structural properties per mg-163f §5.3:
  - `OrderPolytope.convex : Convex ℝ (OrderPolytope α)` — convexity
    via direct verification on the two defining conditions;
  - `OrderPolytope.isClosed : IsClosed (OrderPolytope α)` — closedness
    in the product topology, as a finite-or-infinite intersection
    of preimages of closed sets under continuous evaluations;
  - `OrderPolytope.isBounded : Bornology.IsBounded (OrderPolytope α)`
    — boundedness via containment in the bounded cube `[0,1]^α`
    (`Bornology.IsBounded.pi`);
  - `OrderPolytope.isCompact [Fintype α] : IsCompact (OrderPolytope α)`
    — compactness as a closed subset of the compact cube `[0,1]^α`
    (Tychonoff via `isCompact_univ_pi`);
  - `OrderPolytope.measurableSet [Fintype α] : MeasurableSet (OrderPolytope α)`
    — Borel measurability as a countable intersection of measurable
    half-spaces (`measurableSet_le`, `measurableSet_Icc`).

  The hand-verification on the discrete 3-antichain
  (`α = {a, b, c}` with no nontrivial order relations) is recorded
  by the generic lemma `OrderPolytope.eq_cube_of_discrete : (∀ x y,
  x ≤ y → x = y) → OrderPolytope α = univ.pi (fun _ => Icc 0 1)`,
  applied to a small in-tree type `Three := {a, b, c}` carrying the
  discrete partial order. The `example` line at the bottom of the
  file witnesses `O(Three) = [0,1]^Three`.

* **Implementation note.** The fork-resolution doc mg-163f §5.3
  sketched the basic properties as Lean `instance`s, but `Convex`,
  `IsClosed`, `IsCompact`, `Bornology.IsBounded`, and `MeasurableSet`
  are all `Prop`-valued predicates on a fixed `Set`, not type-class
  arguments — so `instance` syntax does not apply. They are stated
  as named theorems instead; downstream EX-4/EX-5 consumers invoke
  by name, no instance resolution needed. The
  `Mathlib.Order.LowerSet.Basic` import sketched in mg-163f §5.3
  was renamed to `Mathlib.Order.UpperLower.Basic` in this Mathlib
  version (v4.29.1); the file imports the latter.

* **Trust surface impact.** No new axioms. EX-3 does not consume
  `stanley_log_supermod` (the axiom is consumed starting at EX-5).
  The `width3_one_third_two_thirds` headline trust surface is
  unchanged (two named axioms + `native_decide` quintet). The
  sub-α-C arc trust surface is also unchanged (third axiom
  `stanley_log_supermod` consumed only by EX-5 onward).

* **Verdict.** **GREEN.** Build green at this commit
  (`lake build` clean). All basic structural properties populated
  with no `sorry`. Trip-wires not fired: no token blow-up
  (estimated ~80–100k of 300k cap), no mathlib refactor required,
  no build failure, no definition pollution. PM next step: file
  EX-4 scoping ticket (Stanley vertex theorem
  `vertices(O(α)) = {1_I : I ∈ J(α)}`).

### §1.11 EX-1 Option A executed — `stanley_log_supermod` landed as temp axiom

* **Source.** mg-d0fc (this update);
  `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`;
  `lean/AXIOMS.md` (third entry).
* **Statement.** Following Daniel's directive (post-mg-7928 evening
  digest, taken as default-acceptance per
  `feedback_pm_is_mini_ceo_default` and
  `feedback_block_and_report`), PM dispatched Option A: introduce
  `stanley_log_supermod` as a **temporary named project axiom** in
  the `OneThird.LinearExt` namespace, audit-bar-compliant per the
  4-condition table (External / Difficult / Labeled / Low-risk).
  The axiom carries the Stanley 1981 inequality
  `e(I) e(J) ≤ e(I ⊔ J) e(I ⊓ J)` for `I, J : LowerSet α` and a
  finite poset `α`, with `e(K) := |L(α[K])| := numLinExt (subPoset
  (K : Set α))`. The axiom file declares `subPoset` (a wrapped
  subtype with inherited `PartialOrder` / `Fintype` / `DecidableEq`)
  as the only piece of new infrastructure; otherwise the file
  consists of imports, the axiom statement, and inline
  documentation of the audit trail.
* **Trust surface impact.** The third named project axiom is **not**
  consumed by `width3_one_third_two_thirds` or any Step-8 / Step-1
  / F5a / F6 / Path γ pathway. The `width3_one_third_two_thirds`
  headline trust surface remains unchanged: two named axioms
  (`brightwell_sharp_centred`,
  `case3Witness_hasBalancedPair_outOfScope`) + the `native_decide`
  quintet. The third axiom enters the trust surface of the
  *sub-α-C arc only* (consumed by EX-3 onward as hypothesis until
  DH-1 / Option B replacement lands).
* **Deferred.** The corollary `stanley_mu_log_supermod`
  (`μ(I) := e(I) · e(α \ I)` log-supermod on `J(α)`) is deferred
  to a narrow follow-up ticket per the mg-d0fc AMBER verdict.
  Reason: the derivation requires the dual application
  `e(α \ I) e(α \ J) ≤ e(α \ (I ⊓ J)) e(α \ (I ⊔ J))` on
  upper-set complements, which needs either a parallel upper-set
  axiom or a `numLinExt`-on-dual bridge lemma — neither in tree as
  of this commit. EX-3 (chamber-decomposition scoping) does not
  consume the corollary directly, so the deferral does not block
  the next sub-α-C execution ticket.
* **Verdict.** **AMBER** (axiom + AXIOMS.md + state.md complete;
  corollary derivation deferred). Build green at this commit. PM
  files the corollary follow-up ticket and the EX-3 scoping ticket
  next.

### §1.10 EX-1 Session A.2 — variant-3 closure RED, alternative-path deliverable

* **Source.** mg-7928 (this update);
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-induction-closure.md`.
* **Statement.** The simple Bjorner-style closure imagined in
  mg-c7b9 §2.5–§2.6 (lex induction on `(|I ∪ J|, |I △ J|)` with
  Ψ injection bridging) **cannot be made rigorous**. The fresh
  structural fact (mg-7928 §1.2): the IH-bridging step produces
  an inequality with factor `e((I ∩ J) ∪ {m, m'})` on the RHS
  rather than the target's `e(I ∩ J)`, and `e` is monotone
  increasing in the wrong direction for an IH re-application to
  close the gap. mg-7928 §1.3 enumerates candidate sub-pairs
  `(I ∩ J, I ∪ J)`, `((I ∩ J) ∪ {m}, (I ∩ J) ∪ {m'})`,
  `(I, J⁺)`, `(I⁺, J)` — each either has the same lex rank as
  `(I, J)` (recursion non-terminating) or produces an inequality
  whose multiplication with `(\diamond)` does not yield `(\star)`.
  Sharpening the lex parameter (mg-7928 §1.5) does not change the
  shape of the IH-produced inequality, so the obstruction is
  structural, not parameter-choice.
* **Trip-wire fired.** Per polecat brief §5
  ("Bjorner-style fails on a fresh fact … STOP and surface"),
  mg-7928 stopped short of attempting further closure variants
  and surfaced the verdict to PM.
* **Verdict (mg-7928).** **AMBER (variant-3 RED, variant-1
  viable).** PM action item: mail Daniel with Options A–D
  (mg-7928 §3.1).

---

## §2 Retracted — what was claimed and is now disproven

### §2.1 mg-ff7f §2.5: distributivity of `(L(α), ≤_τ)` for fixed `τ`

* **Original claim** (mg-ff7f, commit `6b62a77`, §2.5):
  > for any fixed `τ ∈ L(α)`, `(L(α), ≤_τ)` *is* a distributive
  > lattice (Brightwell §3.5.1).
* **Retracted by.** mg-dc9d §2 (commit `a95020e`). For the
  discrete 3-antichain, `(L(α), ≤_τ)` is the S₃ hexagon, which is
  not distributive. Brightwell §3.5.1 in fact only treats the
  width-2 special case; mg-ff7f misread it as a general statement.
* **Status.** **Retracted.** Path α as scoped by mg-ff7f does not
  survive.

### §2.2 mg-ff7f §6.1 risk classification

* **Original claim.** "Risk 1 — distributivity proof harder than
  expected, LIKELIHOOD: low, MITIGATION: direct adjacent-transposition
  fallback."
* **Retracted by.** mg-dc9d §1. The risk is non-existence of the
  object, not proof difficulty. No fallback can prove a non-existent
  distributive structure.
* **Status.** **Retracted.**

### §2.3 mg-ff7f's downstream LoC estimate (1950–3360 LoC, 9 polecats)

* **Original claim** (mg-ff7f §4.4): Path α total 1950–3360 LoC, 9
  polecats, 2–3 weeks calendar.
* **Retracted by.** mg-dc9d §6 (the entire cascade is blocked).
  The estimate assumed the τ-inversion `DistribLattice` instance
  was inhabitable.
* **Status.** **Retracted.** mg-b10a's earlier 2000–4000 LoC,
  multi-author quarter-scale estimate (for Path sub-α-C, the Hibi
  polytope chamber infrastructure) is now the operative figure if
  Daniel chooses sub-α-C.

### §2.4 mg-dc9d §6.1 sub-α-A's "may admit a different mitigation" hedge

* **Original claim** (mg-dc9d §6 option 1). Sub-α-A might admit a
  per-level FKG with `numLinExt α`-sized normalization for level-`k`
  pullback events, even without a global LE lattice.
* **Retracted by.** mg-21a4 §3 (this current ticket). Concrete
  counterexample on discrete 3-antichain at `k = 1`. Plus an
  independent obstruction (§3.3) on the drops application's `R`
  not being a level event.
* **Status.** **Retracted.**

---

## §3 Open — what is still to verify

### §3.1 Daniel's call: Path γ vs sub-α-C — CLOSED (Path γ confirmed)

* **Question.** Given Path α (mg-ff7f scoping) and sub-α-A
  (mg-21a4 scoping) are both RED, does Daniel prefer
  **Path γ** (retain `case3Witness_hasBalancedPair_outOfScope` as
  a project axiom; cont-4 §6 recommendation) or **sub-α-C**
  (Hibi polytope chamber infrastructure as a multi-author
  quarter-scale mathlib-gap effort)?
* **Status.** **Closed (Path γ confirmed).** Daniel confirmed via
  "onward" reminder 2026-05-07T08:08Z (parsed as default-acceptance
  per `feedback_pm_is_mini_ceo_default`); PM filed
  `lean/AXIOMS.md` framing refresh ticket (mg-bb74, this commit);
  mg-fb16 ship question remains Daniel-scope as project-life-level
  call.
* **Default.** Path γ. The audit-bar economics (cont-4 §6) and the
  forum-readiness sign-off (mg-d7fd) both favour retention.

### §3.2 Sub-α-B (width-2 sub-poset restriction) — likely RED

* **Question.** Is there a sub-class of width-3 posets where the
  drops application can be reduced to width-2 sub-posets, on which
  the τ-inversion lattice IS distributive?
* **Status.** Unscoped. mg-dc9d §6 option 2 named it; case3
  application is intrinsically width-3 (the case3 witness is
  the width-3 antichain, mg-75ef §2). Likely RED.
* **Default.** Not a recommended scoping target unless §3.1's
  Path-γ-vs-sub-α-C call goes a third way.

### §3.3 Brightwell-port standalone (independent of case3)

* **Question.** Could the Brightwell-port axiom-removal be
  pursued without case3 axiom-removal, accepting a partial
  audit-bar improvement?
* **Status.** Same FKG-on-LE prerequisite; same RED. Brightwell-
  port-A consumes the τ-inversion product lattice on
  `L(α) × {1,…,m}` (scoping.md §3.1 step 3); this lattice has the
  same non-distributivity problem on `L(α)` for width-3 `α`.
* **Default.** Brightwell-port also closed under the same
  obstruction. mg-3c06 (the Brightwell mathlib-gap ticket) is
  the long-arc dual. Re-evaluated under sub-α-C: see §3.7 (DH-3).

### §3.4 Sub-α-C scoping — arc-level GREEN; Path A committed (fork resolved mg-163f); EX-3 done (mg-8c66)

* **Source.** mg-91be (sub-α-C high-level scoping);
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`. EX-1
  Session A by mg-c7b9;
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-scoping.md`.
  EX-1 Session A.2 by mg-7928;
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-induction-closure.md`.
* **Question.** Can the Hibi polytope chamber infrastructure for
  FKG-on-LE be ported to Lean as a long-arc multi-polecat effort,
  with the output primitive
  `probEvent'_mono_of_subseteq_upClosed` axiom-eliminating both
  `case3Witness_hasBalancedPair_outOfScope` and
  `brightwell_sharp_centred`?
* **Verdict (arc-level).** **GREEN, upgraded post-mg-163f.**
  6–10 load-bearing primitives (EX-1 through EX-10 in mg-91be
  §5) sketched. Aggregate Path A scope ~4450–7700 LoC
  post-EX-1-landing (mg-163f §2.2; down from 5050–8700) over
  ~12–16 polecat sessions, ~9–15 weeks calendar. The EX-1
  variant-3 closure failure (mg-7928, §1.10) was a sub-level
  RED but did not RED the arc; Option A (mg-d0fc, §1.11) landed
  the temp axiom and unblocked sub-α-C. Post-fork-resolution
  (mg-163f, §1.12), Path A is committed; Path B's level-`k`
  localisation step is AMBER-leaning-RED (no surviving sub-
  formulation). Single material RED risk on Path A is EX-6
  (continuous FKG) which is AMBER with a clean integer-sub-lattice
  fallback for fixed-`α` applications.
* **Verdict (EX-1 sub-level, mg-7928 Session A.2).** **AMBER.**
  Variant-3 closure RED on fresh structural fact (§1.10);
  Variant-1 viable but heavy (~3000–5000 LoC mathlib gap,
  partially amortised against EX-3..EX-7 chamber decomp).
  Variants 2, 4 REJECT.
* **EX-1 progress.** Session A latex done (mg-c7b9). Session A.2
  latex done (mg-7928, this commit). **Four PM action options
  surfaced** (mg-7928 §3.1):
  - **Option A (recommended) — EXECUTED post-mg-d0fc (2026-05-08).**
    DH-1 acceleration + temporary project axiom for
    `stanley_log_supermod`. Sub-α-C rescopes to start at EX-3
    (chamber decomp), with Stanley log-supermod consumed as
    hypothesis until DH-1 lands. mg-d0fc landed the temp axiom
    (`OneThird.LinearExt.stanley_log_supermod`,
    `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`)
    and updated `lean/AXIOMS.md` with the audit-bar 4-condition
    entry. **AMBER verdict** (corollary deferred — see §1.11).
  - **Option B.** Commit to Variant 1 (Stanley 1981 AF). Heavy
    (~3000–5000 LoC mathlib gap) but known. Aligns EX-1 with
    EX-3..EX-7 AF/chamber infrastructure. **Not pursued; subsumed
    by Option A's `axiom`-then-port path.**
  - **Option C.** Session A.3 with literature lookup (Bjorner
    1989, Stanley EC1 §3.5, Aigner Ch. II.4, Brualdi–Mohammadi
    1995). **Not pursued** (Option A executed first).
  - **Option D.** Rescope sub-α-C entirely (RED + lock-in Path γ).
    **Not pursued** (Daniel did not signal sub-α-C abandonment;
    `feedback_long_arcs_are_pm_authority` retained for sub-α-C).
* **Default for next ticket.** **EX-3 done (mg-8c66, this commit;
  see §1.13). PM files EX-4 scoping ticket** (Stanley vertex
  theorem `vertices(O(α)) = {1_I : I ∈ J(α)}`, per mg-163f §5.5).
  EX-3 did **not** consume `stanley_log_supermod` directly (axiom
  is consumed starting at EX-5); the temp axiom remains the
  discharge target of either DH-1 (preferred) or Option B
  (fallback). The corollary `stanley_mu_log_supermod` is no longer
  needed for Path A (Path B-only) and is dropped from the critical
  path.

### §3.5 DH-1 — Stanley log-supermodularity as upstream mathlib PR (refined post-mg-c7b9)

* **Source.** mg-91be §7.1. Refined by mg-c7b9 §4.3 with the
  specific proof-variant target.
* **Question.** Is Stanley's `e(I) e(J) ≤ e(I ∪ J) e(I ∩ J)` on
  `J(α)` upstream-able to mathlib in advance of the Path α arc?
* **Why it matters.** EX-1 is independently valuable as a mathlib
  contribution. If a mathlib reviewer (Yael Dillies maintains
  `Mathlib.Combinatorics.SetFamily.FourFunctions`; natural
  candidate) is interested, ~600–1000 LoC of project-internal
  work moves to mathlib and ~2 polecat sessions are saved on the
  project clock.
* **Refined upstream ask (mg-c7b9, mg-7928).** The variant to
  upstream is **whatever proof variant the mathlib community
  deems appropriate**, likely Stanley 1981 Aleksandrov–Fenchel
  or chain-encoded Ahlswede–Daykin. Specifically, the
  Bjorner 1989 combinatorial route imagined by mg-c7b9 has been
  shown by mg-7928 (§1.10) to **not close** in any obvious way,
  so the upstream PR cannot rely on that variant. Target file:
  `Mathlib/Combinatorics/Order/StanleyLogSupermod.lean`. The PR
  would carry `stanley_log_supermod` (main theorem) plus whatever
  underlying infrastructure the chosen proof needs.
* **Status.** Surfaced to Daniel via PM mail (post-mg-91be merge).
  **Heightened relevance post-mg-7928 (Session A.2):** the
  variant-3 closure failure means the project's mathlib-friendly
  cheap variant is gone. The remaining viable variant (1, AF) has
  ~3000–5000 LoC mathlib gap, so the project-internal cost is now
  much higher than mg-c7b9 estimated. **DH-1 is now the highest-
  leverage path by a wide margin** — a successful mathlib upstream
  PR collapses ~3000–5000 LoC of project work to ~50 LoC consumer.
  Polecat mg-7928 recommends Option A (DH-1 + temporary project
  axiom for `stanley_log_supermod`); see §3.4.

### §3.6 DH-2 — thin-slice for case3 application only

* **Source.** mg-91be §7.2.
* **Question.** Does the case3 application chain need the full
  chamber decomposition for arbitrary finite posets, or only for
  the specific width-3 antichain witnessing case3?
* **Why it matters.** mg-75ef §3 establishes case3 uses drops at a
  specific level `k` for a specific up-closed event derived from
  the case3 bipartite structure. A thin-slice formulation could
  shrink EX-3 through EX-7 by ~30–50%.
* **Status.** Surfaced to Daniel post-mg-91be. Speculative; depends
  on whether the case3 invocation level `k` admits a combinatorial
  special case (e.g., `k = 1` reduces to a single-element-ideal
  event).

### §3.7 DH-3 — Brightwell-port-A vs Brightwell-port-B fork (mg-3c06)

* **Source.** mg-91be §7.3.
* **Question.** Does mg-3c06 (the Brightwell mathlib-gap ticket)
  benefit from sub-α-C as shared infrastructure, or does
  Brightwell require its own sub-α-C-equivalent?
* **Why it matters.** Up to ~1500 LoC saved if EX-7 (drops headline)
  suffices to discharge Brightwell's `eq:sharp-centred`; none if
  Brightwell requires a separate FKG/AD setup on `L(α) × Fin m`.
* **Status.** Surfaced to Daniel post-mg-91be. Concrete ask:
  inspect `step8.tex:1042-1276` and Brightwell §4 to confirm
  whether the centred-sum bound decomposes into a finite
  combination of drops invocations.

### §3.8 DH-4 — continuous FKG/AD acceleration (heightened post-mg-163f)

* **Source.** mg-91be §7.4. Heightened by mg-163f §4.3 post-fork-
  resolution: Path B (the discrete bypass route) is committed
  AMBER-leaning-RED, so EX-6 (continuous FKG/AD on `[0,1]^n`)
  is now the **single largest mathlib-PR-class chunk on the
  critical path** (~1000–2000 LoC).
* **Question.** Is continuous FKG/AD on `[0,1]^n` upstream-able
  to mathlib in advance of EX-6?
* **Why it matters (post-fork).** EX-6 collapses to a citation if
  upstream lands; Path A's heaviest chunk drops by ~1000–2000 LoC.
  Combined with DH-1 (Stanley log-supermod upstream), DH-4 is the
  highest-leverage shortener for Path A.
* **mathlib-PR feasibility (mg-163f §2.3).** No structural
  obstacle. Standard Riemann-sum discretisation route is
  Lean-portable; mathlib has `four_functions_theorem` (discrete
  base case), `MeasureTheory` (integration), `Analysis.Convex`
  (lattice typeclass on `[0,1]^n`). Estimated ~600–800 LoC
  discrete-side scaffolding + ~400–1200 LoC limit argument.
  Natural mathlib reviewers: Yael Dillies, James Gallicchio,
  Bhavik Mehta. Concrete file target:
  `Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`.
* **Fallback if DH-4 doesn't land.** Integer-sub-lattice
  discretisation gives a weaker drops with size-`N` factor; for
  fixed-`α` applications (case3, Brightwell) factor is constant,
  so applications still close. EX-6 RED does not structurally
  collapse Path A.
* **Status.** Heightened post-mg-163f. PM should surface DH-4 to
  Daniel alongside DH-1 in the next digest with the concrete file
  target.

### §3.9 Path B — closed (AMBER-leaning-RED at level-`k` localisation)

* **Source.** mg-163f §3.
* **Question (closed).** Does the discrete coupling (Stanley
  axiom + cross-poset Holley + level-`k` localisation) deliver
  the drops headline at a fixed level `k`?
* **Verdict.** **AMBER-leaning-RED.** Four candidate sub-
  formulations (B-1 through B-4) all hit structural obstructions:
  - **(B-1)** Restrict-to-level-`k` indicator `1[|I| = k]` breaks
    log-supermod (size-mismatch; mg-21a4 §3.2).
  - **(B-2)** Tilted measure `μ_z(I) := μ(I) · z^{|I|}`: gives
    level-averaged inequality with Gaussian envelope, not exact
    level-`k` (mg-21a4 §3.2). Generating-function coefficient
    extraction does not preserve sign (mg-163f §3.4
    counterexample `g(z) = (z-1)^2`).
  - **(B-3)** Level-decorated lattice on `J(α) × Fin (n+1)`:
    under product order, level-locked variant degenerates;
    level-product variant factorises to un-decorated Holley
    with no level-`k` content (mg-163f §3.3).
  - **(B-4)** Direct injection `Ψ' : LE(α[I]) × LE(α[J]) ↪
    LE(α[I ∪ J]) × LE(α[I ∩ J])`: equivalent to Stanley
    log-supermod itself plus a chain-encoded level-`k`
    constraint, which is the original problem in disguise
    (mg-7928 §2.4 + mg-163f §3.4).
* **What survives.** A "summed-over-levels" reduced Path B is
  derivable, but it does not specialise to a fixed-`k` drops as
  required by case3 and Brightwell applications.
* **Status.** **Closed.** No further investigation warranted. Path
  A is the operative path.

---

## §4 Path forward — best estimate (working hypothesis post-mg-21a4)

### §4.1 PM's working hypothesis

**Path γ (retain).** This is the recommended successor and the
default if Daniel doesn't push back:

* `case3Witness_hasBalancedPair_outOfScope` stays on the trust
  surface, as in `lean/AXIOMS.md:226–454`.
* `brightwell_sharp_centred` stays on the trust surface, as in
  `lean/AXIOMS.md:13–225`.
* Forum-post draft (mg-d7fd) already articulates a two-named-axiom
  trust surface; minor doc edit may shift framing from "scheduled
  for replacement" to "definitively retained" (~10–20 LoC).
* mg-fb16 (the "unhold" ticket) becomes Daniel's call to either
  release the hold (Path γ confirmed) or convert to sub-α-C tracker
  (long arc).
* No new long-arc ticket is filed unless Daniel chooses sub-α-C.

### §4.2 Sub-options under consideration

| Option   | What it costs                                                                              | What it buys                                            | Recommended? |
|----------|--------------------------------------------------------------------------------------------|---------------------------------------------------------|--------------|
| Path γ   | One paragraph in forum-post; 0 Lean LoC; 0 polecats                                        | Two named project axioms remain on trust surface        | **Yes.** Default. |
| sub-α-A  | RED — cannot be executed                                                                    | n/a                                                     | n/a (RED).   |
| sub-α-B  | Likely RED for width-3 case3; would need a separate scoping if Daniel insists              | Possibly partial (only width-2 case3 sub-instances)     | No.          |
| sub-α-C  | 2000–4000 LoC + 1450–2700 LoC application chain; ~6–12 polecats; multi-author quarter scale | Both axioms removed; trust surface = mathlib trio + native-decide pair | No, unless axiom-elim is hard requirement. |

### §4.3 Decision points and triggers

* **Today (post-mg-21a4 merge).** PM mails Daniel with the verdict
  summary and the path-γ-vs-α-C call.
* **If Daniel chooses Path γ.** No new tickets. mg-fb16 unhold
  released. Optionally: a small docs-only ticket to update
  `lean/AXIOMS.md` framing (~10–20 LoC, 30-min polecat).
* **If Daniel chooses sub-α-C.** PM files
  `mathlib-gap-FKG-on-LE` (working name) as a long-arc multi-polecat
  ticket. Calendar weeks-to-months. Daniel reserves multi-polecat
  capacity. cont-4 §6 already articulates this option.

### §4.4 What this state.md predicts will be added next

After Daniel's path-γ-vs-α-C decision lands:

* **§3.1 closes.** Either as "Path γ confirmed; mg-fb16 released"
  or "sub-α-C committed; long-arc ticket filed".
* **§4 collapses** to the chosen path with operational details.
* **§1 grows** if sub-α-C is chosen and partial mathlib-gap
  results land (e.g., the τ-inversion `DistribLattice` instance
  finally lands as a mathlib PR; the chamber decomposition lands
  as a port).
* **§2 stays** as the historical record of retracted claims.

(Closed by mg-91be: per Daniel directive 2026-05-07T16:06Z, **both
Path γ and sub-α-C are simultaneously committed** — Path γ remains
the recommended status-quo for ship velocity, and sub-α-C is
dispatched as the long arc to full formalisation. mg-fb16 unhold
remains released. §3.1 stays "Path γ confirmed"; §3.4 captures
sub-α-C in flight.)

### §4.5 Sub-α-C decision points and triggers (post-mg-91be scoping)

* **Today (post-mg-91be merge).** PM mails Daniel with the
  AMBER-leaning-GREEN verdict and the four DH leverage points
  (§3.5 through §3.8). PM files EX-1 (Stanley log-supermodularity
  port) as the first execution ticket.
* **Post-mg-7928 (Session A.2) — Daniel decision required.**
  Variant-3 (Bjorner combinatorial) closure RED'd on fresh
  structural fact (§1.10). PM mails Daniel with the four
  EX-1 options surfaced by mg-7928 §3.1:
  - **Option A (polecat recommendation).** DH-1 acceleration +
    temporary project axiom for `stanley_log_supermod` in
    `lean/AXIOMS.md`. Net impact on Path γ: zero. Net impact on
    sub-α-C Path A: rescope to start at EX-3, defer EX-1 until
    DH-1 lands.
  - **Option B.** Commit to Variant 1 (AF). Heavy
    (~3000–5000 LoC mathlib gap) but known to work; aligns with
    EX-3..EX-7 AF/chamber infrastructure.
  - **Option C.** Session A.3 literature lookup (~100–200k
    tokens, scoping-only, risk: convergence to A or B).
  - **Option D.** Rescope sub-α-C entirely (lock in Path γ).
    Daniel's authority per `feedback_long_arcs_are_pm_authority`.
  Daniel's call gates whether sub-α-C proceeds, and on which
  variant.
* **Post-mg-d0fc (Option A executed) — decision point closed.**
  PM committed Option A per `feedback_block_and_report` +
  `feedback_pm_is_mini_ceo_default` (decide + inform; do not
  second-guess polecat recommendations on Lean tickets). Daniel's
  default-acceptance window applied; sub-α-C proceeds via the
  Option A pathway (temp axiom + DH-1 surface). DH-1 surfaces to
  Daniel via the evening digest; PM does not block on Daniel
  acknowledgment for EX-3 dispatch. **mg-d0fc landed the temp
  axiom** (§1.11); state.md and `lean/AXIOMS.md` updated; build
  green; AMBER verdict (corollary deferred). PM next: file the
  corollary follow-up + EX-3 scoping ticket.
* **Post-EX-1 land — Path-A-vs-Path-B fork resolved (mg-163f).**
  Per mg-163f §3.3 + §3.4, Path B's level-`k` localisation step
  is AMBER-leaning-RED on a sharper survey of the four candidate
  sub-formulations (B-1 restrict-to-level, B-2 tilted measure,
  B-3 level-decorated lattice, B-4 direct injection). PM commits
  **Path A** (~4450–7700 LoC post-EX-1-landing, ~12–16 polecat
  sessions, ~9–15 weeks calendar). EX-3 (order polytope `O(α)`
  as Lean type) is the next execution ticket; spec drafted in
  mg-163f §5. Decision point closed.
* **Post-mg-8c66 (EX-3 executed) — decision point closed.**
  Order polytope `OrderPolytope α` landed in
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  with the five basic structural properties (convex, closed,
  bounded, compact under `[Fintype α]`, measurable under
  `[Fintype α]`) populated as named theorems plus the discrete-
  3-antichain hand-verification. Build green. No new axioms
  introduced; Stanley temp axiom not consumed at EX-3 (it enters
  starting at EX-5). PM next step: file EX-4 scoping ticket
  (Stanley vertex theorem `vertices(O(α)) = {1_I : I ∈ J(α)}`).
* **Post-EX-7 land.** EX-8 (case3-port-2) and EX-9
  (Brightwell-port-A) execute in parallel; both consume the drops
  headline and have no mutual dependencies. EX-10 (axiom-removal)
  follows sequentially after both.
* **DH triggers (parallel to EX-1, dispatched on Daniel input).**
  - DH-1 lands → `mathlib upstream Stanley log-supermod` → EX-1
    moves to mathlib; subtract ~2 sessions.
  - DH-2 confirmed → thin-slice case3 specialisation → halves
    EX-3 through EX-5 work.
  - DH-3 amortisation confirmed → EX-9 reduces to ~500–800 LoC
    specialisation; otherwise spawn separate mg-3c06-class arc.
  - DH-4 alternative → EX-6 (continuous FKG) bypassed; subtract
    ~2–3 sessions.
* **Trip-wires for the long arc** (per polecat brief §6).
  - Aggregate scope > 10000 LoC: STOP, mail Daniel; sub-α-C may
    be the wrong scope.
  - New structural obstruction REDs sub-α-C: STOP, mail Daniel;
    Path γ becomes the only feasible direction.
  - Calendar overrun > 6 months without an EX-7 land: STOP, scope
    review.

---

## §5 References (chronological by Path α arc)

* mg-b10a (`256f0da`) — A8-S2-cont-4 STOP report, FKG-on-LE
  obstruction first surfaced.
  `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`.
* mg-ff7f (`6b62a77`) — Path α scoping (RETRACTED §2.5).
  `docs/path-alpha-scoping/scoping.md`.
* mg-dc9d (`a95020e`) — Hibi-1 STOP report, mg-ff7f §2.5 retraction.
  `docs/path-alpha-execution-arc/hibi-1-stop-report.md`.
* mg-21a4 (`f862b76`) — sub-α-A scoping, RED verdict.
  `docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`.
* mg-bb74 (`73ed85e`) — `lean/AXIOMS.md` framing refresh
  ("definitively retained").
* mg-91be (`bb450a4`) — sub-α-C scoping, AMBER leaning GREEN.
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`.
* mg-c7b9 (`4b5b1ba`) — EX-1 Session A scoping, AMBER (variant 3
  chosen, closure not yet verified).
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-scoping.md`.
* mg-7928 (`6e07904`) — EX-1 Session A.2, AMBER (variant 3
  closure RED'd; Options A–D for Daniel decision).
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-induction-closure.md`.
* mg-d0fc (`00cbc2d`) — EX-1 Option A executed: temp axiom
  `OneThird.LinearExt.stanley_log_supermod` landed; AMBER
  (corollary `stanley_mu_log_supermod` deferred to follow-up).
  `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`,
  `lean/AXIOMS.md` (third entry).
* mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolution: GREEN-A.
  Path A committed (~4450–7700 LoC post-EX-1-landing); Path B
  AMBER-leaning-RED at level-`k` localisation step (four sub-
  formulations all RED). EX-3 spec drafted.
  `docs/path-alpha-execution-arc/path-A-vs-path-B-fork-resolution.md`.
* mg-8c66 (this commit) — EX-3 executed: `OrderPolytope α`
  defined with basic structural properties (convex, closed,
  bounded, compact, measurable) and discrete-3-antichain
  hand-verification. Build green; no new axioms.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`.

---

*This is a living document. Future Path-α-flavoured polecat tickets
must (a) read this first, (b) update §1 / §2 / §3 / §4 with their
findings, (c) append a "Last update" line to the header. The
discipline applies starting now (mg-21a4).*
