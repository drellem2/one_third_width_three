# OneThird LIB — does the sole-crux inequality follow from a known poset correlation inequality? (bounded, dedup-first scoping)

**Work item:** `mg-f9f4` (high, repo `one_third_width_three`). Daniel full-speed GO, no
gate. Continuation of the spectral / near-ordinal-sum chain: `mg-b0a6` (kill-shot, ALIVE)
→ `mg-3ce3` (L4, GREEN) → `mg-8b64` (BK→transport transfer, AMBER/GREEN-in-regime) →
`mg-7ae7` (reverse-Cheeger proof attempt, PRODUCTIVE WALL, reduced everything to **LIB**).
This is a **scoping** probe, not a proof grind: route the crux against the known
correlation-inequality toolbox, dedup against the walled Čech/F-series framings, deliver a
routed verdict, then **STOP**. Reuses `mg-7ae7`'s reduction verbatim; does **not** re-derive it.

---

## Verdict: **(b) GENUINELY HARD / NEW — known correlation inequalities are provably insufficient; LIB is the irreducible open crux. Recommend STOP + strategic reassessment with Daniel.**

Not verdict (a): no named inequality closes LIB, and none supplies an exact remaining lemma
that would (the skeptical bar for (a) is not met — see §3, §4). Not verdict (c): LIB is **not
literally** any of the ~21 walled Čech/F-series framings — the closed-form reverse-Cheeger
reduction (`E[inv_e]=O(n/γ)`) is a genuinely **new handle**. But its resolution *by a known
correlation inequality* is **pre-walled** by the project's own F3 structural fact
(the published `[0.276, 1/3)` Linial–Kahn / Brightwell width-3 gap: correlation-inequality +
width-3 specialisation alone has not reached `1/3` in 30+ years), and LIB **converges on the
same joint-law crux** the Čech program stalled on (F31 RED-chain-locality). §5.

The one lever the toolbox does **not** rule out is a **bespoke** width-3 3-chain transfer /
decay-of-correlations argument (route 3 of `mg-7ae7` §7) — but that is a multi-session
research construction, *not* an off-the-shelf correlation inequality, so it does not change
this verdict. It is the natural subject of the strategic reassessment.

---

## 0. What LIB is, restated exactly (from `mg-7ae7`, not re-derived)

`P` a width-3 indecomposable **γ-counterexample** on `[n]`, `γ∈(0,1/3]`, all incomparable
pairs frozen (`δ(P)<1/3`): every `x∥y` has `p_xy=Pr_σ[x<_σ y]∈[γ,1/3)∪(2/3,1−γ]` under the
uniform linear-extension (LE) measure `σ`. Distinguished order `e=(1,…,n)` orients every
strong majority; for `i<_e j` incomparable, the **backward probability** `Pr[j<_σ i]<1/3`.

> **LIB (Linear Inversion Bound).**
> `E_σ[inv_e(σ)] = Σ_{i<_e j, i∥j} Pr[j<_σ i] = O(n/γ)`.

`mg-7ae7` proves (rigorously, re-verified numerically) that the entire Buser-type transport
transfer — hence the whole spectral / near-ordinal-sum program — is **equivalent** to LIB:
`1−λ_std(P) ≤ O(E[inv_e]/n²)`, so the target `1−λ_std ≤ C/(γn)` holds **iff** `E[inv_e]=O(n/γ)`.

### 0.1 The two facts that shape every tool assessment

These two observations, both already in `mg-7ae7` but sharpened here, determine which tools
can possibly apply.

**Fact A — LIB is a bound on a SUM OF MARGINALS, not a correlation quantity.**
`E[inv_e] = Σ_{pairs} Pr[j<_σ i]` is *exactly determined by the pairwise marginals*
(linearity of expectation). Correlations **between distinct pairs do not enter** `E[inv_e]`
at all — they affect only `Var(inv_e)`. A correlation inequality (FKG, XYZ, AD, Holley,
Graham, Brightwell) relates a **joint** probability `Pr[A∩B]` to a product `Pr[A]·Pr[B]`; it
does **not**, by itself, upper-bound a single marginal `Pr[j<_σ i]`. So no correlation
inequality bounds `E[inv_e]` *directly*. Any route must instead use correlation to
**bootstrap the marginals downward** — i.e. force the backward marginals to *decay* along a
chain so their sum is linear.

**Fact B — the required marginal decay is GEOMETRIC, and freezing alone gives only `O(n²)`.**
Width 3 = 3 Dilworth chains; cross-chain incomparable pairs number `Θ(n²)` (up to `ab+bc+ca
≤ n²/3` for chain sizes `a,b,c`). Each backward marginal is `<1/3`, so naively `E[inv_e] =
O(n²)`. For the fixed chain pair `(C_a,C_b)` the matrix `M[i][j] := Pr[v_j<_σ u_i]` is
**monotone** (`mg-7ae7` Lemma 4.1: decreasing in `j`, monotone in `i`). Its total mass is
`O(n)` **iff** the decay is geometric (`M[i][j] ≤ ρ^{|i−j|}`, `ρ<1`); a `1/dist` tail gives
`O(n log n)`, a fat tail gives `Θ(n²)`. **LIB ⟺ geometric decay of the backward-probability
matrix along chains.** This is the precise joint-law feature a proof must produce.

---

## 1. Tool-by-tool assessment

The ticket's named toolbox, each judged on **(i) does it apply to the uniform LE measure**
and **(ii) does it deliver the `O(n)` (linear, not quadratic) bound in-regime**. The bar
(`feedback_empirical_green_is_not_proven`): a plausibility argument is not a route; a route
must name the exact inequality **and** the exact remaining lemma.

### 1.1 FKG / Holley / Ahlswede–Daykin — **does not apply to the target quantity; wrong sign.**

- **(i) Applies to LE?** Yes, in the standard way: the uniform LE measure pulls back to a
  log-supermodular (FKG-condition) measure on the distributive lattice `J(P)` of order
  ideals / on the order-polytope discretisation. This is exactly the input the project
  *already* formalised — `FKG.fkg_uniform_initialLowerSet` (mg-9ece, `cd75ef1`), used inside
  the paper proof of `brightwell_sharp_centred` (`step8.tex:1101–1244`). So FKG/AD is a live,
  in-tree tool, not a missing one.
- **(ii) Gives `O(n)`?** **No, and structurally cannot.** FKG/AD produce **positive**
  correlation of increasing events: `Pr[A∩B] ≥ Pr[A]Pr[B]` for up-events `A,B` on `J(P)`.
  Against LIB this is doubly useless:
  - By **Fact A**, `E[inv_e]` is a sum of marginals — a covariance sign gives *nothing* about
    it.
  - Worse, for the **decay** route (Fact B), positive correlation is the **wrong sign**. The
    backward events `{v_j<_σ u_i}` along a chain are, by XYZ (§1.2), **positively** correlated,
    so `Pr[v_{j+1}<_σ u_i | v_j<_σ u_i] ≥ Pr[v_{j+1}<_σ u_i]` — conditioning *raises* the next
    backward probability, giving **slower** decay, never geometric. FKG/AD push the matrix
    `M[i][j]` toward a **fat** tail, the `Θ(n²)` failure mode.
- **Verdict: RED.** FKG/AD is a positive-correlation tool; LIB needs marginal decay (a
  negative-dependence / mixing phenomenon). Right measure, wrong direction.

### 1.2 Shepp's XYZ inequality — **applies, but is the obstruction, not the tool.**

- **(i) Applies?** Yes — XYZ (Shepp 1982, proved *via* Ahlswede–Daykin) is *specifically* the
  statement that for the uniform LE measure the events `{x<_σ z}` and `{y<_σ z}` are
  **positively** correlated: `Pr[x<_σ z ∧ y<_σ z] ≥ Pr[x<_σ z]·Pr[y<_σ z]`. These are exactly
  the backward-type events LIB sums.
- **(ii) Gives `O(n)`?** **No — it certifies the wrong sign at the heart of LIB.** XYZ *proves*
  that the backward events cluster positively, which is precisely why the naive marginal sum
  cannot be beaten by soft averaging and why the decay route (Fact B) has no free
  positive-correlation hammer. XYZ is the theorem that makes LIB hard, not the theorem that
  closes it.
- **Verdict: RED (diagnostic).** XYZ pins the LE measure firmly on the positive-correlation
  side of the ledger. It rules out the negative-association shortcut (§1.5) as a *general* LE
  fact.

### 1.3 Kahn–Saks correlation / entropy machinery — **per-pair existence tool; not a sum bound.**

- **(i) Applies?** Yes, and it is the closest classical machine to the 1/3–2/3 problem
  itself. Kahn–Saks (1984) use log-concavity of the single-element height sequence
  `h_x(k):=#{LE with x in position k}` (log-concave by Stanley 1981 via
  Aleksandrov–Fenchel), plus an entropy/exchange argument, to prove a **balanced pair**
  exists (balance `∈[3/11,8/11]`). Brightwell's per-term covariance bound
  `|Cov_μ(1_A,S)| ≤ f̄/m` (`step8.tex:1246–1271`; Brightwell 1999 Thm 4.1) is the same family
  and is exactly the project's `brightwell_sharp_centred`.
- **(ii) Gives `O(n)`?** **No — three independent reasons.**
  1. **Wrong output type.** Kahn–Saks / Brightwell bound the balance of **one** pair (an
     `O(1/|Q|)`-type per-pair statement). LIB is a bound on the **sum over `Θ(n²)` pairs**.
     There is no summation/telescoping in the Kahn–Saks argument that yields `Σ_pairs`.
  2. **Per-pair bound is already known-vacuous here (project fact F2).** The Brightwell
     per-element bound is `2/|Q|`; at the relevant width-3 scale it needs `|Q|≥12` to clear
     `1/3` and is *vacuous* on the small factors (`project_two_track_program_active` F2:
     "Brightwell vacuity at K=2, `|Q|≤6`"). The same vacuity blocks using it per-pair to force
     small backward marginals.
  3. **Log-concavity of `h_x` does not bound displacement.** `E[σ⁻¹(x)]−rank_e(x) = Σ_y(
     backward marginals at `x`)`, and `E|σ⁻¹(x)−rank_e(x)|` is the displacement LIB needs
     bounded. Log-concavity gives **unimodality** of `h_x`, not **concentration**:
     `Var(σ⁻¹(x))` can be `Θ(n²)` for a log-concave `h_x` (an element weakly tied to a long
     chain). Concentration to `O(1/γ²)` is exactly the frozen-joint-law content that
     log-concavity + marginals do not supply.
- **Verdict: RED.** Kahn–Saks/Brightwell is a per-pair existence engine (it powers the whole
  1/3–2/3 lower bound and the in-tree axiom), but it has no mechanism to bound the summed
  backward mass, and its per-pair constant is vacuous at the width-3 factor scale.

### 1.4 Fishburn's / Graham's correlation inequalities — **more positive-correlation; same failure.**

- **(i) Applies?** Yes — Graham (1983, "Applications of the FKG inequality and its relatives")
  and Fishburn's / Winkler's correlation inequalities are further FKG/AD consequences for LE
  measures, of the form `Pr[a<b, c<d] ≥ Pr[a<b]Pr[c<d]` (or Fishburn's cross-inequalities).
- **(ii) Gives `O(n)`?** **No.** All are **positive-correlation** statements about joint
  events; by Fact A they say nothing about `Σ` of marginals, and by Fact B they carry the
  wrong sign for decay. They are refinements of the §1.1/§1.2 tools, not a new mechanism.
- **Verdict: RED.** Same class as FKG/XYZ.

### 1.5 Negative dependence / strong Rayleigh / real-stable for LE measures — **does not apply.**

This is the *only* family with the **right sign** (negative dependence → the "spread-out /
anti-clustering" that could force decay), so it deserves the sharpest kill.

- **(i) Applies to the uniform LE measure?** **No — provably not.** Strong-Rayleigh /
  negatively-associated theory (Borcea–Brändén–Liggett 2009) governs measures on `{0,1}^N`
  with a **real-stable** generating polynomial (determinantal, uniform spanning tree,
  symmetric exclusion). Two obstructions:
  1. **No ground set.** The uniform LE measure lives on `S_n` / the order polytope, not on
     `{0,1}^N`. The natural indicator variables `{1[a<_σ b]}` are *not* the coordinates of a
     product space with a real-stable generating polynomial; no such polynomial for the LE
     measure is known or expected.
  2. **The LE measure is provably NOT negatively associated.** §1.2 (XYZ) exhibits
     **positively** correlated increasing events for the LE measure — the defining violation of
     negative association. So even the qualitative hypothesis of the negative-dependence
     toolbox fails for LE measures in general.
- **(ii) Gives `O(n)`?** Moot — inapplicable at step (i).
- **Verdict: RED (decisive).** The sign-correct toolbox does not reach the LE measure. The
  frozen hypothesis might create *local* negative dependence on a specific 3-chain interface,
  but that is not any known strong-Rayleigh structure — it is the bespoke object of §4.

### 1.6 Summary table

| tool | applies to LE measure? | gives `O(n)` in-regime? | why it fails on LIB |
|---|---|---|---|
| FKG / Holley / Ahlswede–Daykin | yes (in-tree, mg-9ece) | **no** | positive-correlation; wrong sign for decay; nothing on `Σ` marginals (Fact A) |
| Shepp XYZ | yes | **no** | *proves* the wrong sign — it is the obstruction |
| Kahn–Saks / Brightwell | yes (in-tree axiom) | **no** | per-pair existence, not a sum; constant vacuous at `|Q|≤6` (F2); log-concavity ≠ concentration |
| Fishburn / Graham / Winkler | yes | **no** | same positive-correlation class |
| strong Rayleigh / real-stable / neg-assoc | **no** | — | LE measure has no real-stable form and is positively correlated (XYZ) |

**Every off-the-shelf poset correlation inequality is either the wrong sign (positive
correlation) for the decay LIB needs, or the wrong output type (per-pair, not a sum), or
inapplicable to the LE measure (no strong-Rayleigh structure).** None delivers `O(n/γ)`.

---

## 2. Why the failure is structural, not a gap in the survey

The five families above are not an arbitrary list — they partition the mechanisms available.
LIB requires **`Θ(n²)`-many `<1/3` marginals to sum to `O(n)`**, i.e. **geometric decay of a
monotone backward-probability matrix** (Fact B). The only mechanisms that produce
summable decay of correlations are:

1. **Negative dependence / anti-concentration** — ruled out for LE measures (§1.5): they are
   positively correlated (XYZ).
2. **A spectral gap of a transfer operator / mixing** — this is a *bespoke* dynamical fact
   about the width-3 3-chain interleaving, not a named correlation inequality. It is
   `mg-7ae7` route 3 (geometric freezing), and it is **circular at the abstract level**: the
   transfer operator has a gap iff LIB-type decay holds. Producing the gap *is* the open work.
3. **Positive-correlation inequalities** (FKG/XYZ/AD/Graham/Brightwell/Kahn–Saks) — the wrong
   sign; they cannot manufacture decay and in fact certify clustering (§1.1–1.4).

So the toolbox gap is not "we didn't find the right inequality" — it is that the *sign* of the
LE measure's correlation structure (positive, by XYZ) is the opposite of what a summable-decay
proof needs, and the sign-correct machinery (strong Rayleigh) does not reach the LE measure.
This is why `mg-7ae7` §4.2's two-atom counterexample is decisive: it satisfies **all** the
pairwise-frozen marginals *and* Lemma 4.1 monotonicity, yet has `Θ(n²)` inversions — so LIB
must use a joint-law feature of *genuine* width-3 LE geometry that no marginal-level or
positive-correlation tool can see.

---

## 3. Could any tool give a *conditional* route (a partial (a))?

Checked, to honour the skeptical bar (a claimed route must name the exact remaining lemma):

- **FKG on a single chain-pair sub-lattice, chained.** One might hope to run FKG on the
  2-chain interleaving lattice and chain per-step bounds into geometric decay. This is exactly
  `mg-7ae7` route 1. It fails at the sign (§1.1): FKG gives `≥`, decay needs `≤`. The "exact
  remaining lemma" would be an *upper* bound on a conditional backward probability — which FKG
  does not provide and XYZ contradicts. **No route.**
- **Kahn–Saks summed over positions.** One might sum the per-pair `2/m` bound. But `Σ_pairs
  2/|Q|` over `Θ(n²)` pairs with `|Q|=O(n)` gives `O(n)` **only if** the pairs live in
  factors of size `Θ(n)` *and* the bound were non-vacuous — but F2 says it is vacuous at the
  small-factor scale, and the summation double-counts across overlapping `Q`'s. No valid
  telescoping exists. **No route.**
- **A bespoke width-3 transfer-operator gap** (route 3). This *could* be a genuine route, but
  it is **not a known inequality** — it is new mathematics (a decay-of-correlations theorem for
  the frozen width-3 3-chain interleaving). Naming it as "the remaining lemma" would be
  honest, but it is precisely LIB in transfer-operator clothing, so it does not discharge the
  crux; it relocates it. This is the subject of the strategic reassessment (§6), **not** a
  verdict-(a) route.

No conditional (a) survives the bar. The verdict stands at (b).

---

## 4. The exact joint-law feature LIB needs (naming the crux, per ticket step 3)

LIB is the irreducible open statement. The **specific** reason known correlation inequalities
fail, stated precisely:

> LIB requires that the uniform LE measure of a **frozen width-3 poset** exhibit **geometric
> decay of backward probabilities along each Dilworth chain** — a *negative-dependence /
> spatial-mixing* property. The LE measure is **positively** correlated (Shepp XYZ), so it
> admits **no** general negative-dependence structure (not strong Rayleigh, not negatively
> associated); and the frozen marginals alone are consistent with `Θ(n²)` inversions
> (`mg-7ae7` §4.2 two-atom law). Therefore LIB must be extracted from the **specific geometry
> of the width-3 order polytope under all-pairs-freezing** — a property strictly finer than
> (a) the pairwise marginals, (b) any positive-correlation inequality, and (c) the single
> log-concave height distribution `h_x`. No such extraction tool exists in the correlation-
> inequality literature.

The frozen hypothesis is what could make the *local* interface negatively dependent (each
element pinned between its `e`-neighbours with prob `>2/3`), but turning that local pinning
into global geometric decay is exactly the unproven transfer/mixing statement.

---

## 5. Dedup — LIB against the walled Čech/F-series framings (mandatory)

Per ticket step 2 and `feedback_dedup_against_closed_arcs`. Three walled bodies checked.

### 5.1 The ~21 walled framings (`project_two_track_program_active`) — LIB is not among them, but F3 pre-walls its correlation-inequality resolution.

The 2026-05-04 three-arc search (arcs 1.0/2.0/3.0, `mg-b666`/`mg-80ab`/`mg-65e1`) tried ~21
framings (8 ε-close-to-ordinal-sum definitions + 12 strategy alternatives + compound-aut
tracks), all failing at one of three structural facts **F1/F2/F3**. LIB is a *different object*
(a spectral-transport-derived inversion bound, filed 2026-07-13, post-dating that search), so
it is **not one of the 21**. But two of the three facts bear directly:

- **F3 — the published `[0.276, 1/3)` gap (Linial–Kahn / Brightwell pump).** Verbatim from the
  memory: *"correlation-inequality + width-3 specialisation alone doesn't reach `1/3`"*, and
  tightening to `1/3` for width 3 *"has not been done in 30+ years."* **LIB is exactly a
  correlation inequality for width-3 LE.** So the claim "close LIB with a known correlation
  inequality" is **pre-walled by F3**: it asks the toolbox to do in one polecat what the
  literature has not done in three decades. This is the single strongest external reason the
  §1 verdict is RED across the board, and it is a *project-internal, already-accepted* fact.
- **F2 — Brightwell vacuity at `|Q|≤6`.** Directly kills the per-pair Kahn–Saks route (§1.3(2)).

**Dedup finding:** LIB is *new* as a statement, but its "solve-by-known-inequality" resolution
is a fresh instance of the F3 barrier the project already documented. Not a repeat of a
specific walled framing; a fresh collision with a known structural wall.

### 5.2 The master-inequality attempts (`mg-fd0d` / `mg-a1aa` / `mg-2f8c`) — direct precedent that off-the-shelf LE monotonicity fails.

The project already tried a **universal master correlation inequality on width-3 LE**
(`probEvent'_mono_of_subseteq_upClosed`, EX-7 arc). `mg-2f8c` found it **mathematically FALSE**
(133,180 violations / 1,431,564 instances; **2-antichain** minimal counterexample); `mg-fd0d`
halted on that trip-wire; `mg-a1aa` retreated to a *refined* master with S-side restrictions.
This is direct, in-project evidence that **a universal off-the-shelf correlation-monotonicity
on the LE measure does not hold without restriction** — the same lesson §1 reaches for LIB.
Not the same statement (that arc was about a monotonicity master for the Brightwell axiom, not
the inversion sum), but a strong dedup signal: *do not re-attempt a universal LE correlation
inequality expecting it to hold; the project has a counterexample on file.*

### 5.3 The Čech/F-series program (`project_cech_bias_program`) — LIB converges on the same crux; not identical.

The Čech program (F17+F18 anchor: only cohomology on `Δ(PPF_n)` is sign-like; F29/F30
construct the bad-cut Čech class; **F31 RED-chain-locality**: the bad-cut class lies in
`ker(Φ_*)`, killed by chain-locality). `mg-7ae7` §4.2/§5 already assert LIB is *"the same crux
as BK-bad-mixing and the Čech/F-series program"*: **all three converge on control of the joint
law of a random linear extension of a frozen width-3 poset, beyond its pairwise marginals.**

- **Is LIB *literally* a walled Čech framing (verdict c)?** **No.** The Čech program is
  cohomological (derive a contradiction from a bad-cut cohomology class); LIB is
  probabilistic/analytic (bound a sum of backward marginals). F31's wall is *chain-locality of
  `Φ_*`*; LIB's wall is *positive-correlation of the LE measure*. Different mathematical
  surfaces.
- **Do they share the underlying difficulty?** **Yes.** Both need the *frozen-width-3 joint
  law* controlled beyond marginals. The `mg-7ae7` reverse-Cheeger reduction is the **genuinely
  new handle**: it is a *closed-form* target (`E[inv_e]=O(n/γ)`) that the Čech program never
  produced. That novelty is why this is verdict (b), not (c) — but the novelty is in the
  *handle*, not in a *new tool that closes it*.

**Net dedup:** LIB is a **new expression** of the shared joint-law crux (do not treat it as a
re-run of any specific walled arc), but **known correlation inequalities closing it is
pre-walled** by F3, and the LE measure's positive correlation (XYZ) matches the sign
obstruction the Čech side hit in a different dialect. Consistent with
`feedback_u1_has_multiple_dialects`: the same wall keeps reappearing in new clothing.

---

## 6. Recommendation — STOP + strategic reassessment (per ticket, verdict (b))

Per the ticket ("if (b)/(c), the right move is a strategic reassessment with Daniel, not more
attempts") and `feedback_revisit_only_on_path_specific_blockers`:

1. **STOP the "close LIB with a known correlation inequality" line.** §1–§5 establish it is
   RED across the toolbox for a *structural* reason (sign + output-type + no strong-Rayleigh),
   reinforced by the project's own F3 and the `mg-2f8c` universal-master counterexample. Do
   **not** file per-tool proof attempts (FKG-chain, Kahn–Saks-sum, etc.); each is disposed of
   above.
2. **Bring the CONVERGENCE to Daniel as the strategic object.** The real finding is that the
   spectral (LIB), BK-bad-mixing, and Čech/F-series programs **all reduce to one statement**:
   *control the joint law of a uniform LE of a frozen width-3 poset beyond its pairwise
   marginals.* `mg-7ae7`'s closed-form `E[inv_e]=O(n/γ)` is the **cleanest** and **most
   concrete** expression of that crux to date (an inequality, not a cohomology class). Daniel's
   call: whether to (a) formally unify the two programs around LIB as the single shared target,
   or (b) accept it as the named irreducible residual.
3. **The one lever left open** (for Daniel to authorise or decline, **not** to file
   unilaterally): a **bespoke geometric-decay / transfer-operator argument** for the frozen
   width-3 3-chain interleaving (`mg-7ae7` route 3). It is the only mechanism with the right
   sign that is *not* ruled out — because it is new mathematics, not an off-the-shelf
   inequality. Scope: multi-session research push (a decay-of-correlations theorem for a
   bounded-width order-polytope Gibbs-type measure), high risk, no known precedent for the
   exact statement. This is a `project_onethird_two_milestones`/vision-direction call, not a
   polecat call.
4. **Do NOT** re-open the walled Čech arcs (F31 RED) or re-attempt a universal LE correlation
   master (`mg-2f8c` FALSE). Both are on file as walls.

**Bottom line for Daniel.** LIB does **not** follow from any known poset correlation
inequality. The reason is structural and clean: `E[inv_e]` is a **sum of marginals** (so
correlation inequalities do not touch it directly), and the only way to beat the naive `O(n²)`
is **geometric decay** of backward probabilities — a *negative-dependence / mixing* property
that the uniform LE measure **provably lacks in general** (it is positively correlated, by
Shepp's XYZ, and has no strong-Rayleigh structure). The one un-ruled-out lever, a bespoke
width-3 transfer-operator decay theorem, is new mathematics, not a citation — so LIB is the
**irreducible open crux**, now expressed in its sharpest closed form. The strategically
valuable fact is the **convergence**: spectral, BK-mixing, and Čech all bottom out at this one
joint-law statement. Recommend a reassessment with Daniel on whether to unify the programs
around LIB or accept it as the named residual — not more correlation-inequality attempts.

---

## 7. Cross-references

- **`mg-7ae7`** — `docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md` (the reduction; LIB
  statement §4; routes §7; two-atom counterexample §4.2). Reused verbatim, not re-derived.
- **`mg-8b64`** — `docs/OneThird-L1b-BK-Transport-Transfer-Probe.md` (single-cut L1b FALSE /
  in-regime GREEN; the 166 refuters).
- **`mg-b0a6` / `mg-3ce3`** — spectral kill-shot / L4 stability probes.
- **`compatibility-geometry-hecke-brightwell-scoping.md`** (mg-e396) — FKG/AD + per-term
  Kahn–Saks/Brightwell as the *in-tree* machine for `brightwell_sharp_centred`; confirms these
  are per-pair tools (§1.1, §1.3 here).
- **`compatibility-geometry-cuts-by-pairs-scoping.md`** (mg-d4ed) — the "Buser-type reverse
  Cheeger" gap `mg-7ae7` closed in closed form; §5.2 literature search located no precedent.
- **`project_two_track_program_active`** — F1/F2/F3 structural facts; F3 pre-walls the
  correlation-inequality resolution (§5.1 here).
- **`mg-fd0d` / `mg-a1aa` / `mg-2f8c`** — universal LE master inequality FALSE (§5.2 here).
- **`project_cech_bias_program`** — F17+F18 anchor, F29/F30/F31 chain, F31 RED-chain-locality;
  LIB converges on the shared joint-law crux (§5.3 here).
- **`feedback_empirical_green_is_not_proven`**, **`feedback_dedup_against_closed_arcs`**,
  **`feedback_u1_has_multiple_dialects`** — the discipline this scoping honours.
- **Literature.** Shepp, *The XYZ conjecture and the FKG inequality*, Ann. Prob. 1982;
  Ahlswede–Daykin 1978; Kahn–Saks, *Balancing poset extensions*, Order 1984; Stanley,
  *Two combinatorial applications of the Aleksandrov–Fenchel inequalities*, JCTA 1981;
  Brightwell 1989 / 1999; Graham, *Applications of the FKG inequality and its relatives*, 1983;
  Borcea–Brändén–Liggett, *Negative dependence and the geometry of polynomials*, JAMS 2009.
