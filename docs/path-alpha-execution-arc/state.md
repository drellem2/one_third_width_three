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
  the long-arc dual.

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

---

## §5 References (chronological by Path α arc)

* mg-b10a (`256f0da`) — A8-S2-cont-4 STOP report, FKG-on-LE
  obstruction first surfaced.
  `docs/a8-s2-cont-execution-arc/cont-4-stop-report.md`.
* mg-ff7f (`6b62a77`) — Path α scoping (RETRACTED §2.5).
  `docs/path-alpha-scoping/scoping.md`.
* mg-dc9d (`a95020e`) — Hibi-1 STOP report, mg-ff7f §2.5 retraction.
  `docs/path-alpha-execution-arc/hibi-1-stop-report.md`.
* mg-21a4 (this commit) — sub-α-A scoping, RED verdict.
  `docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`.

---

*This is a living document. Future Path-α-flavoured polecat tickets
must (a) read this first, (b) update §1 / §2 / §3 / §4 with their
findings, (c) append a "Last update" line to the header. The
discipline applies starting now (mg-21a4).*
