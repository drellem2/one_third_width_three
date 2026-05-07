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

### §3.4 Sub-α-C scoping in flight — AMBER leaning GREEN

* **Source.** mg-91be (this update);
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`.
* **Question.** Can the Hibi polytope chamber infrastructure for
  FKG-on-LE be ported to Lean as a long-arc multi-polecat effort,
  with the output primitive
  `probEvent'_mono_of_subseteq_upClosed` axiom-eliminating both
  `case3Witness_hasBalancedPair_outOfScope` and
  `brightwell_sharp_centred`?
* **Verdict.** **AMBER leaning GREEN.** 6–10 load-bearing primitives
  (EX-1 through EX-10 in mg-91be §5) sketched with explicit Lean
  signatures; aggregate Path A scope ~5050–8700 LoC over ~13–17
  polecat sessions, ~9–15 weeks calendar steady state. Within
  factor 1.3 of state.md §4.2's "2000–4000 + 1450–2700 LoC"
  working figure. Path B alternative (avoid polytopes via
  Stanley + tilted Holley) at ~2900–4900 LoC if the level-`k`
  localisation step closes — currently unknown.
* **Default.** PM files **EX-1 (Stanley log-supermodularity port)**
  as the first execution ticket — it is load-bearing for both
  Path A and Path B and is the most isolatable mathlib-friendly
  chunk. After EX-1 lands, the Path-A-vs-Path-B fork can be
  re-evaluated.

### §3.5 DH-1 — Stanley log-supermodularity as upstream mathlib PR

* **Source.** mg-91be §7.1.
* **Question.** Is Stanley's `e(I) e(J) ≤ e(I ∪ J) e(I ∩ J)` on
  `J(α)` upstream-able to mathlib in advance of the Path α arc?
* **Why it matters.** EX-1 is independently valuable as a mathlib
  contribution. If a mathlib reviewer (Yael Dillies maintains
  `Mathlib.Combinatorics.SetFamily.FourFunctions`; natural
  candidate) is interested, ~600–1000 LoC of project-internal
  work moves to mathlib and ~2 polecat sessions are saved on the
  project clock.
* **Status.** Surfaced to Daniel via PM mail (post-mg-91be merge).
  Concrete ask: open Zulip discussion or DM with the FKG-area
  maintainer. The combinatorial proof (Daykin 1990 / Bjorner
  1989) is the mathlib-friendly form; Aleksandrov–Fenchel
  (Stanley 1981) is heavier and not suitable for upstream.

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

### §3.8 DH-4 — continuous FKG/AD acceleration

* **Source.** mg-91be §7.4.
* **Question.** Is there a working pathway via discrete FKG that
  avoids continuous FKG (EX-6) entirely?
* **Why it matters.** EX-6 (continuous FKG on `[0,1]^n`) is the
  single largest mathlib-PR-class chunk of Path A
  (~1000–2000 LoC). Bypass routes: Path B (level-`k` localisation
  on `J(α)` discretely), or discretisation via Riemann sums on an
  integer sub-lattice of `[0,1]^n`.
* **Status.** Surfaced to Daniel post-mg-91be. Most speculative of
  the four DH leverage points; surface only if Daniel has prior
  knowledge of mathlib continuous FKG efforts.

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
* **Post-EX-1 land.** Re-evaluate Path A vs Path B fork based on
  how amenable Stanley's argument is to combinatorial Lean
  formalisation. If the proof reveals a clean combinatorial
  level-`k` localisation: pursue Path B (~2900–4900 LoC,
  ~6–10 weeks). Otherwise: pursue Path A (~5050–8700 LoC,
  ~9–15 weeks).
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
* mg-91be (this commit) — sub-α-C scoping, AMBER leaning GREEN.
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`.

---

*This is a living document. Future Path-α-flavoured polecat tickets
must (a) read this first, (b) update §1 / §2 / §3 / §4 with their
findings, (c) append a "Last update" line to the header. The
discipline applies starting now (mg-21a4).*
