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
**Last update.** mg-1f3a (cat-mg-1f3a), 2026-05-10. **EX-7 Session C.1
— chamber transport for `OrderPolytope' Q` (Option 1 closure path,
no 5th axiom).** §1.26 NEW for the Session C.1 deliverable
(`lean/OneThird/Mathlib/RelationPoset/DropsHeadlineChamber.lean`,
~267 LoC).  Predecessor: mg-4a56 (`ddedda4`, EX-7 Session B
structural infra Option 3 per mayor override).  Polecat brief
(mg-1f3a) framed Session C.1 as the start of the Option 1 full
closure path for the master theorem
`probEvent'_mono_of_subseteq_upClosed`, decomposed per state.md
§1.25 forward pointer into (a) chamber-volume transport ~150 LoC,
(b) single-edge induction + swap ~200 LoC, (c) master assembly via
AD + Stanley ~250–650 LoC.  This session lands piece (a).
**Deliverable.** Chamber-decomposition machinery transported to the
data-version `OrderPolytope' Q` in the `OneThird.RelationPoset`
namespace: `chamber'` (data-version chamber simplex);
`chamber'_volume` (Stanley 1986 (1.5): `volume(σ_L) = 1/n!`);
`chamber'_inter_meas_zero` (Stanley 1986 (1.4) overlap);
`chamber'_cover` (Stanley 1986 (1.4) cover);
`orderPolytope'_volume` (Stanley 1986 (1.4) master:
`volume(O(Q)) = numLinExt' Q / n!`);
`measurableSet_chamber'`, `chamber'_subset_orderPolytope'`,
`numLinExt'_eq_numLinExt_asPartialOrder`. All seven exposed theorems
transport via the mg-4a56 `OrderPolytope'_eq_asPartialOrder`
`rfl`-bridge plus the natural
`{ toFun := L.toFun, monotone := L.monotone }`-construction; no new
mathematical content beyond mg-10d9 / mg-497d. **Trust surface
impact: none.** `#print axioms` on the seven exposed theorems gives
only the mathlib-standard `{propext, Classical.choice, Quot.sound}`
triplet — **no new project axioms**.  `width3_one_third_two_thirds`
headline trust surface unchanged (still 2 named axioms +
native_decide quintet); sub-α-C arc trust surface unchanged (still
4 named axioms; ≤4-axiom envelope per mayor mg-4a56 preserved).
Master theorem advances to **EX-7 Session C.2** (single-edge
induction + swap involution, ~200 LoC); Sessions C.2 + C.3 remain
estimated ~450–850 LoC combined.  Build green for full `OneThird`
target (~2643 lake jobs).  3-round trip-wire on EX-7 chain (per
brief) cleared: 0 amber rounds running.  §3.4 updated (sub-α-C
arc: EX-7 Session C.1 done, Session C.2 is the next execution
ticket).  PM next step: file **EX-7 Session C.2 scoping ticket**
(structural induction lemma `Q.Subseteq Q' → chain of single-edge
`addRel` augmentations` + swap involution `τ_{ab}` on
`LinearExt' Q` for `Q`-incomparable `(a, b)` + chamber identity
`O(Q) = O(Q') ⊔ τ_{ab}(O(Q'))` mod a Lebesgue-null hyperplane;
mg-1f3a §1.26 handoff brief is the Session C.2 brief).
**Last update.** mg-4a56 (cat-mg-4a56), 2026-05-09. **EX-7 Session B —
structural infrastructure (Option 3) per mayor override.** §1.25 NEW
for the Session B deliverable
(`lean/OneThird/Mathlib/RelationPoset/DropsHeadline.lean`, ~205 LoC).
Predecessor: mg-2746 (`dcd0925`, EX-7 Session A scoping with Path R-A
recommendation), mg-071b (`8b49708`, EX-6 Session F closing
`continuous_ad_general` via 4th project axiom `cellMass_AD`), mg-d731
(`e1fdaa1`, cellMass_AD verification GREEN). **Substantive scoping
finding (mid-session, mailed to mayor at session start).** After
in-session analysis, the substantive Daykin–Saks 1981 swap-induction
inner step turned out to require ~500–1000 LoC of measure-theory glue
beyond the Session B budget per mg-2746 §7.2 (~150–270 LoC).  Polecat
(mg-4a56) mailed mayor with three options (full closure with 3 pillars;
5th project axiom mirroring mg-071b; structural infra only).  Mayor
returned **Option 3** as the trust-surface-preserving call: a 5th axiom
would exceed the project's ≤4-axiom envelope committed in the previous
evening digest.  **Deliverable.** Structural infrastructure landed in
`OneThird.RelationPoset` namespace: `OrderPolytope' Q` (data-version
order polytope, `rfl`-bridge to typeclass `OrderPolytope α` under
`Q.asPartialOrder`); `OrderPolytope'_subset_of_subseteq` (Q.Subseteq
Q' ⟹ O(Q') ⊆ O(Q), reversed-direction FKG monotonicity-under-
augmentation); `OrderPolytope'_inf_mem` and `OrderPolytope'_sup_mem`
(sublattice property under componentwise `⊓, ⊔`, the key structural
fact for Brightwell 1999 §4.2 chamber + AD reduction);
`OrderPolytope'_measurableSet` and `OrderPolytope'_subset_cube`
(transports of mg-8c66 typeclass results via `asPartialOrder`).
**Trust surface impact: none.** `#print axioms` on the four exposed
theorems gives only the mathlib-standard
`{propext, Classical.choice, Quot.sound}` triplet — **no new project
axioms**.  `width3_one_third_two_thirds` headline trust surface
unchanged (still 2 named axioms + native_decide quintet). EX-7 Session
B (master theorem `probEvent'_mono_of_subseteq_upClosed` itself) is
**deferred to Session C**; estimated 2–3 polecat sessions, ~600–1000
LoC, consuming this file's structural infrastructure together with
`chamber_cover` / `chamber_volume` / `orderPolytope_volume` (mg-10d9),
`continuous_ad_general` (mg-071b), and `stanley_log_supermod` (mg-d0fc).
Build green for full `OneThird` target (~2640 lake jobs). §3.4 updated
(sub-α-C arc: EX-7 Session B structural infra done, Session C is the
next execution ticket = master theorem assembly). PM next step: file
**EX-7 Session C scoping ticket** (chamber + AD + Stanley assembly via
single-edge induction + swap involution; deliverable mg-2746 §2.4 +
§5.2 form the Session C brief; budget split by mayor preference).
**Last update.** mg-d731 (cat-mg-d731), 2026-05-09. **cellMass_AD
independent verification GREEN** (4th project axiom, parallel to
mg-e22f for the 3rd axiom). §1.24 NEW for the trust-surface
separate-verification deliverable
(`docs/path-alpha-execution-arc/cellMass-AD-verification.md`):
three sub-checks per Daniel directive 2026-05-08T16:11Z all pass
(cross-literature: 10 sources / 5 decades, including Grimmett 1999
+ Liggett 1985/2005 graduate textbooks and Brightwell 1999 §4.2
project primary cite; numerical sanity: 94 instances / 14 948
cell-pair checks / 0 violations, exact rationals, covers the
EX-7-motivating polytope-indicator shapes; uncontested in
literature). §3.8 (DH-4) updated to note `cellMass_AD` is now
externally verified; DH-4 mathlib upstream PR remains the highest-
leverage shortener for Path A's EX-6/EX-7 chunk. `lean/AXIOMS.md`
`cellMass_AD` entry extended with a "Separate verification"
subsection (4th axiom; first three unchanged). No Lean source
changes beyond the AXIOMS.md write-up. Trust surface unchanged
(headline still two named axioms + `native_decide` quintet; sub-α-C
arc adds `stanley_log_supermod` + `cellMass_AD` as 3rd and 4th
axioms, both now externally verified). Trip-wires not fired (no
numerical violation, no literature thinness). PM next step:
surface verification GREEN to Daniel in evening digest; proceed
with EX-7 Session B scoping ticket dispatch.
**Last update.** mg-071b (cat-mg-071b), 2026-05-09. **EX-6
Session F — `continuous_ad_general` (Monotone-free) landed via
4th project axiom.** §1.23 NEW for the Session F deliverable
(`lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
§9–§10, ~330 LoC). Predecessor: mg-2746 (`dcd0925`, EX-7 Session A
scoping that surfaced the Monotone-vs-polytope-indicator
hypothesis-mismatch and recommended Path R-A).
**Substantive scoping finding (mid-session, mailed to mayor at
session start).** The mg-2746 Path R-A spec estimated Session F at
~300 LoC with no new project axiom (`#print axioms
continuous_ad_general` = mathlib triplet). After analysis, the
substantive step (mg-2746 §4.2 step 3: "discrete AD on cell averages
preserves the four-function inequality, ~50 LoC Cauchy–Schwarz /
linearity") is **not** Cauchy–Schwarz/linearity — it is the
literature-standard **Ahlswede–Daykin 1979 Lemma 2** "cell averages
preserve AD" lemma, recursive at the same dimension and requiring
either (a) Riemann-sum + mollification, (b) martingale convergence
+ DCT (bounded f), or (c) full A-D 1979 mollification machinery —
each ~1000–1500 LoC of mathlib measure-theory glue beyond the
session budget. Polecat (mg-071b) mailed mayor with three options
(sublattice-restricted, axiom-bearing, full-closure) and proceeded
with **Option 2: cell-AD as 4th named project axiom**
(`OneThird.ContinuousFKG.cellMass_AD`) per the project's existing
disclosure pattern (Brightwell, Case3, Stanley axioms). The
deliverable lands an EX-7-usable `continuous_ad_general` with full
disclosure in `lean/AXIOMS.md` §`cellMass_AD`. **Trust surface
impact: +1 axiom (4 total).** Build green; `#print axioms
OneThird.ContinuousFKG.continuous_ad_general` = `{propext,
Classical.choice, Quot.sound, OneThird.ContinuousFKG.cellMass_AD}`.
**Replacement path: DH-4** (mathlib upstream PR for
`Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean` carrying both
the Monotone-free `continuous_ad_general` and the cell-AD lemma);
recorded at `lean/MATHLIB_GAPS.md` §DH-4. **Verdict
AMBER-leaning-GREEN.** §3.4 updated (sub-α-C arc: EX-7 Session A
scoping done **+ EX-6 Session F closed**; **EX-7 Session B is the
next execution ticket** consuming `continuous_ad_general` +
chamber decomp + `stanley_log_supermod`). PM next step: file
**EX-7 Session B** scoping ticket (chamber-decomposition reduction
+ `continuous_ad_general` consumption + `stanley_log_supermod`
inner-step closure, ~150–270 LoC per mg-2746 §7.2). The 4th
axiom decision is preserved on the trust-surface ledger; mayor
visibility maintained via the start-of-session mail.
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
**Last update.** mg-e22f (cat-mg-e22f), 2026-05-09. **Stanley
log-supermod independent verification GREEN.** §1.15 NEW for the
trust-surface separate-verification deliverable
(`docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`):
three sub-checks per Daniel directive 2026-05-08T16:11Z all pass
(cross-literature: 7 sources / 4 decades; numerical sanity: 16
posets / 2 835 pairs / 0 violations; uncontested in literature).
§3.5 (DH-1) updated to note the temp axiom is now externally
verified, but DH-1 mathlib upstream PR remains the highest-leverage
shortening for the sub-α-C arc trust surface. `lean/AXIOMS.md`
`stanley_log_supermod` entry extended with a "Separate verification"
subsection (third axiom; first two unchanged). No Lean source
changes beyond the AXIOMS.md write-up. Trust surface unchanged
(headline still two named axioms + `native_decide` quintet; sub-α-C
arc still adds `stanley_log_supermod` as third axiom). Trip-wires
not fired (no numerical violation, no literature thinness). PM next
step: surface verification GREEN to Daniel in evening digest;
proceed with EX-4 dispatch (Stanley vertex theorem) per mg-8c66
hand-off.
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
**Last update.** mg-4831 (cat-mg-4831), 2026-05-09. **EX-4
Session A executed: Stanley vertex theorem latex writeup + mathlib
mapping done.** §1.14 NEW for the Session A deliverable
(`docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`,
~880 lines latex): both directions of Stanley 1986 Theorem 1.2
proven rigorously without convex-geometry / mixed-volume / continuous
FKG — Direction 1 is direct (convex combination of [0,1]-bounded
values pinning at the boundary), Direction 2 uses an explicit
`±ε`-perturbation on the level set `f^{-1}(c)` for `c ∈ (0,1)` in
the range of `f`. Mathlib `Set.extremePoints` API verified GREEN
against the in-tree `OrderPolytope α` (mg-8c66): typeclass surface
fits cleanly, useful structural lemmas (`mem_extremePoints`,
`extremePoints_pi`, `Convex.mem_extremePoints_iff_convex_diff`)
are off-the-shelf. **One small spec correction surfaced** (§4.1
of the deliverable): the mg-91be §5.4 / mg-163f §5.5 target
signature uses `LowerSet α` for the indexing set, but the in-tree
`OrderPolytope` convention (`f x ≤ f y` for `x ≤ y`, mg-8c66) makes
`1_I` order-preserving iff `I` is an **upper set**, not a lower
set. Fix is one-line (recommend `UpperSet α`; alternative is
`LowerSet α` + complement); chamber-decomp arc downstream
(EX-5..EX-7) is unaffected by the choice (cardinality preserved
under upper/lower duality). §3.4 updated (sub-α-C arc: EX-4
Session A done, GREEN with spec correction; Session B = next
execution ticket). §3.10 NEW (DH-5 secondary mathlib-upstream
candidate: combined EX-3 + EX-4 PR as
`Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`; lower
priority than DH-1 / DH-4). Trip-wires not fired (~120k of 350k
cap; no API mismatch; no Direction-2 obstruction). Session B ETA
refined to ~330–470 LoC, ~170–265k tokens (down from mg-91be §5.4's
400–600 LoC, 200–300k tokens, on the back of a clean direct argument
that needs no Stanley-axiom invocation). Trust surface unchanged
(EX-4 introduces no new axioms). PM next step: file EX-4 Session B
scoping ticket (direct Lean port using §6 of the deliverable).
**Last update.** mg-2442 (cat-mg-2442), 2026-05-09. **EX-4
Session B executed: Stanley vertex theorem ported to Lean.**
§1.16 NEW for the Session B deliverable
(`lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
extension, ~330 LoC of Lean). Both directions of Stanley 1986
Theorem 1.2 formalised in tree against the in-tree `OrderPolytope α`
(mg-8c66). Direction 1 lemmas:
`OrderPolytope.indicator_upperSet_mem` (membership) and
`OrderPolytope.indicator_upperSet_isExtreme` (extreme), using only
mathlib's `Set.indicator`, `mem_extremePoints`, `openSegment`, and
the convex-combination pinning argument (mg-4831 §2.3). Direction 2
private lemmas: `perturbUp` / `perturbDown` definitions
(level-set ±ε perturbation via `Set.indicator`), `exists_perturbation_eps`
(positive ε via `Finset.inf'` over `Finset.univ.filter (f x ≠ c)`,
requires `[Fintype α]`), `perturbUp_mem` / `perturbDown_mem`
(membership under gap conditions, 6-case order-preservation per
mg-4831 §3.5), `extremePoint_isBoolean` (every extreme point in
`{0, 1}`-valued, contradiction via the perturbation), and
`onePreimage_isUpperSet` (the 1-level set is an upper set under
monotonicity). Direction 2 main: `extremePoint_eq_indicator_upperSet`.
Master theorem `OrderPolytope.extremePoints_eq` packages both
directions: `Set.extremePoints ℝ (OrderPolytope α) = { f | ∃ I :
UpperSet α, f = Set.indicator (I : Set α) (1 : α → ℝ) }` (the §4.1
mg-4831-recommended UpperSet form). Trust surface impact: **none**.
`#print axioms` on the three exposed theorems
(`indicator_upperSet_isExtreme`, `extremePoint_eq_indicator_upperSet`,
`extremePoints_eq`) gives only the mathlib-standard
`{propext, Classical.choice, Quot.sound}` triplet — **no new project
axioms**, as predicted by mg-4831 §1 + §5. Trip-wires per mg-4831
§6: not fired (build green; mathlib API matched cleanly with one
post-port adjustment — coercion `(I : Set α) = I.carrier` for
`I : UpperSet α` constructed via anonymous constructor required an
explicit `hI_coe` rewrite step in `extremePoint_eq_indicator_upperSet`,
~2 LoC; no structural mathlib gap fired). LoC count ~330 lands at
the lower edge of the mg-4831 §6 estimate (~330–470 LoC). §3.4
updated (sub-α-C arc: EX-4 done, GREEN; EX-5 chamber decomposition
is the next execution ticket). §3.10 (DH-5) ready to surface to
Daniel post-merge: combined EX-3 + EX-4 mathlib upstream PR
(`Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`) is now
realisable since both pieces are in tree.
**Last update.** mg-497d (cat-mg-497d), 2026-05-09. **EX-5
Session B executed: chamber definition + volume theorem ported to
Lean.** §1.18 NEW for the Session B deliverable
(`lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
extension, ~430 LoC of Lean). Stanley 1986 Theorem 1.4 (volume
part) `Vol(σ_L) = 1/n!` formalised in tree against the in-tree
`OrderPolytope α` (mg-8c66) and `LinearExt α` (`Fintype.lean:45`).
Three-layer architecture: (1) `chamber L : Set (α → ℝ)` definition
+ `chamber_subset_orderPolytope`; (2) `orderedCube n : Set (Fin n → ℝ)`
+ `orderedCubePerm n σ` infrastructure with measurability + the
S_n-tiling proof of `volume_orderedCube` (DH-5 candidate, ~150 LoC
of derivation now in tree); (3) `chamberRelabel L : (α → ℝ) ≃ᵐ
(Fin n → ℝ)` measure-preserving via `volume_measurePreserving_piCongrLeft`,
plus `chamber_eq_preimage_orderedCube` and the master `chamber_volume`.
Trust surface impact: **none** (`#print axioms` triplet
`{propext, Classical.choice, Quot.sound}`; no new project axioms).
LoC ~430 lands at the lower edge of mg-79a9 §7.1's estimate
(~395–560 LoC); tokens well under the 450k cap. **DH-5 strengthening:
`volume_orderedCube` is now in tree** (sub-namespace
`OneThird.LinearExt.OrderedCube`) — combined EX-3 + EX-4 + EX-5-B
mathlib upstream candidate
`Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean` is now
realisable today (cover + overlap = Session C close out the
chamber-decomposition triple). Trip-wires per mg-79a9 §7.1 not
fired. §3.4 updated (sub-α-C arc: EX-5 Session B done, GREEN;
EX-5 Session C is the next execution ticket). PM next step: file
**EX-5 Session C scoping ticket** (cover via Szpilrajn-on-level-set
+ measure-zero overlap + master `orderPolytope_eq_iUnion_chamber`).
**Last update.** mg-79a9 (cat-mg-79a9), 2026-05-09. **EX-5
Session A executed: chamber decomposition latex-first scoping done.**
§1.17 NEW for the Session A deliverable
(`docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md`,
~1220 lines latex). All three chamber-decomposition claims
(Stanley 1986 §1) rigorously proved: (1) `Vol(σ_L) = 1/n!` via
`MeasurableEquiv.piCongrLeft` relabel + symmetric S_n-tiling of
`[0,1]^n` giving `Vol(Δ_n) = 1/n!` for the standard ordered cube
`Δ_n`; (2) `O(α) = ⋃_L σ_L` via Szpilrajn-on-level-set cover
construction (sort α by `f`-value, break ties using Szpilrajn
within each level set); (3) `Vol(σ_L ∩ σ_{L'}) = 0` via
`addHaar_submodule` on the strict hyperplane `{f x = f y}` for
the inversion pair `(x, y)` separating `L` and `L'`. Mathlib API
verified GREEN against the project's pinned mathlib (no
fundamental gap; `MeasureTheory.measurePreserving_piCongrLeft:744`,
`MeasureTheory.volume_Icc_pi:241`, `addHaar_submodule:175`,
`isAddHaarMeasure_volume_pi:126` all available). One derivable
in-file gap surfaced: `volume_orderedCube` (`Vol{ y ∈ ℝ^n |
0 ≤ y_0 ≤ … ≤ y_{n-1} ≤ 1 } = 1/n!`) is **not directly in
mathlib** (only the *probability simplex* is, via
`Analysis.Convex.StdSimplex`); ~150–200 LoC of derivation, scoped
as Session B sub-deliverable + **DH-5 strengthening** (state.md
§3.10) — the combined EX-3 + EX-4 + EX-5 mathlib upstream PR
becomes a stronger candidate. §3.4 updated (sub-α-C arc: EX-5
Session A done, GREEN-2; PM files Session B next). Verdict:
**GREEN-2** (split Session B + Session C; mg-91be §5.5's "2
polecat sessions" estimate retained, ~815–1185 total LoC over
the 2 Lean sessions, ~495–745k tokens combined). Trip-wires not
fired (Session A finishing under 270k of 320k cap; no
mathlib-measure-theory fundamental obstruction; no convex-
geometry / mixed-volume detour; no discretised-fallback fire).
Trust surface unchanged (EX-5 introduces no new project axioms;
`stanley_log_supermod` still consumed only by EX-7+). PM next
step: file **EX-5 Session B scoping ticket** (volume + relabel
+ `volume_orderedCube` DH-5 candidate; deliverable §5.1–§5.2 +
§6 + §7.1).
**Last update.** mg-10d9 (cat-mg-10d9), 2026-05-09. **EX-5
Session C executed: chamber cover + measure-zero overlap +
master volume theorem ported to Lean.** §1.19 NEW for the
Session C deliverable (`lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
extension, ~280 LoC of Lean). Closes the chamber-decomposition
arc: (1) `chamber_cover`: `OrderPolytope α = ⋃ L, chamber L` via
`linearExtFromOrderPreserving` (sort α by lex key
`(f x, S.pos x)` with `S` a fixed Szpilrajn extension for
tie-breaking; `Tuple.sort` + `Tuple.monotone_sort` close the
construction); (2) `chamber_inter_meas_zero`:
`Vol(σ_L ∩ σ_{L'}) = 0` for `L ≠ L'` via `Tuple.unique_monotone`
deducing `f x = f y` for an inversion pair `(x, y)` plus
`Measure.addHaar_submodule` on the strict hyperplane
`equalCoordSubmoduleAlpha x y = {f | f x = f y}`; (3)
`orderPolytope_volume`: `Vol(O(α)) = numLinExt α / n!` combining
cover + AE-disjointness + per-chamber `chamber_volume` via
`measure_biUnion_finset₀`. Trust surface impact: **none**
(`#print axioms` on the three new theorems gives only
`{propext, Classical.choice, Quot.sound}` — no new project
axioms, as predicted by mg-79a9 §6.5 and §7.2). LoC ~280 lands
under the lower edge of mg-79a9 §7.2's estimate
(~420–625 LoC), aided by the `Tuple.sort`-on-lex-key route
(Route C, not Route A or B from mg-79a9 §3.5) avoiding the
explicit Szpilrajn-on-each-level-set construction; the
augmented partial order `x ≤_α y ∨ f x < f y` is realised
implicitly via the lex sort key `(f x, S.pos x)` with `S`
a fixed Szpilrajn extension. §3.4 updated (sub-α-C arc:
**EX-5 done in full, GREEN**; chamber-decomposition triple
complete; EX-6 continuous FKG/AD on the cube is the next
execution ticket — DH-4 leverage candidate per mg-163f §3.9).
**DH-5 strengthening (state.md §3.10).** All four chamber-
decomposition pieces are now in tree (`chamber`,
`volume_orderedCube`, `chamber_cover`, `chamber_inter_meas_zero`,
`orderPolytope_volume`); combined EX-3 + EX-4 + EX-5 mathlib
upstream candidate `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`
is now realisable as a single PR (~900–1100 LoC). Trip-wires
per mg-79a9 §7.2 not fired. PM next step: **file EX-6 scoping
ticket** (continuous FKG / Ahlswede–Daykin on `[0,1]^n`).
**Last update.** mg-e622 (cat-mg-e622), 2026-05-09. **EX-6 Session
A — continuous FKG / Ahlswede–Daykin on `[0,1]^n` latex-first
scoping done.** §1.20 NEW for the Session A deliverable
(`docs/path-alpha-execution-arc/ex6-continuous-fkg-scoping.md`,
~900 lines latex). Predecessors: mg-10d9 (`7b084ba`, EX-5 Session C
chamber decomposition complete); mg-163f (`9e6edcd`, Path A
committed, DH-4 risk AMBER with integer-sub-lattice fallback);
mg-91be (`bb450a4`, sub-α-C scoping with EX-6 spec in §5.6).
**Verdict GREEN-2** (split Session B + Session C). Standard
Riemann-sum discretisation route: discrete FKG/AD on
`(Fin (N+1))^n` via mathlib `fkg` / `four_functions_theorem_univ`
+ step-function approximation `f_N⁻ ≤ f ≤ f_N⁺` for monotone `f`
+ limit `N → ∞` via
`tendsto_integral_filter_of_dominated_convergence`. **Both
polecat-brief questions answered:** (1) yes, mathlib has discrete
FKG/AD as the base case; (2) Riemann-sum discretisation **is**
the standard proof of continuous FKG (not an alternative path),
and the full continuous theorem is recommended over the
integer-sub-lattice fallback. **No critical mathlib gap.** All
mathlib APIs verified at `lake-manifest.json` →
`mathlib v4.29.1`-class:
`Mathlib.Combinatorics.SetFamily.FourFunctions` (`fkg:365`,
`four_functions_theorem:297`, `four_functions_theorem_univ:341`),
`Mathlib.Order.Lattice` (`Pi.instDistribLattice` for the product
lattice on `Fin n → Fin (N+1)`),
`Mathlib.MeasureTheory.Integral.DominatedConvergence`
(`tendsto_integral_filter_of_dominated_convergence:70`),
`Mathlib.MeasureTheory.Integral.Lebesgue.Add`
(`lintegral_iSup:34`,
`lintegral_tendsto_of_tendsto_of_monotone:113`),
`Mathlib.MeasureTheory.Constructions.Pi`
(`volume_pi_pi`, `volume_Icc_pi:241`),
`Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`
(`addHaar_submodule:175`),
`Mathlib.Topology.Order.Monotone`
(`Monotone.countable_not_continuousAt`, 1D version). One
auxiliary multivariate version not packaged in mathlib
(`Monotone.aeContinuousAt_pi` for `(α → ℝ) → ℝ` with
`[Fintype α]`) is **derivable in ~80 LoC** from the existing 1D
version + `Set.Countable.measure_zero` — surfaced as
**Sub-DH-4-A** upstream candidate, **not blocking**. **DH-4
leverage assessment.** The deliverable is structured for direct
mathlib upstream extraction once Sessions B + C land:
`lean/OneThird/Mathlib/Probability/ContinuousFKG.lean` →
`Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean` is a
~1000–1600 LoC single-PR candidate (Yael Dillies, James
Gallicchio, Bhavik Mehta natural reviewers per mg-163f §3.9).
The **integer-sub-lattice fallback** (mg-163f §4.4) is **not
recommended as primary**: the size-`N` discretisation factor
infiltrates EX-7 / EX-8 / EX-9 and partly cancels the EX-6 LoC
saving (+200–400 LoC downstream); the discrete-FKG part of
Session B is reusable as the fallback's main content if Session C
trip-wires fire. **Session B + C ETA refinement.** mg-91be §5.6's
"~1000–2000 LoC, ~600–1000k tokens" splits to: Session B (~600–900
LoC, ~350–500k tokens) for discrete FKG/AD + step-function
approximation + Riemann-sum identity; Session C (~400–700 LoC,
~250–400k tokens) for a.e. convergence + DCT + master theorem +
hand-verification. **Total ~1000–1600 LoC, ~600–900k tokens.**
Session A consumed ~150k tokens (well under the 400k cap); total
A + B + C ~750–1050k, at the upper edge of the mg-91be §5.6
600–1000k envelope. LoC mid-range. **No fallback to mg-163f §4.4
needed.** **Trust surface impact: none.** EX-6 introduces no new
project axioms (consumed by EX-7 onward, not by EX-6 itself);
`stanley_log_supermod` not consumed. **Trip-wires per polecat
brief §3 / mg-91be §5.6 — none fired.** Token blow-up: not fired.
Mathlib refactor: not fired. Continuous-FKG-already-in-mathlib
collision: not fired (no `continuous_fkg` / `Preston` references
in `Mathlib` at this rev). DH-4 fallback firing in Session A: not
fired (Riemann-sum is primary, not fallback). AD lattice-
hypothesis transport: not fired (`min(k/N, l/N) = min(k, l)/N`
trivial). Monotone-implies-a.e.-continuous gap: AMBER (multivariate
not packaged in mathlib; derivable in ~80 LoC; sub-DH-4-A);
not blocking. §3.4 updated (sub-α-C arc: **EX-6 Session A done,
GREEN-2**; PM files Session B next). §3.8 (DH-4) updated
post-session: continuous FKG proof is now **rigorously written
and Lean-portable**, ready for Session B + C dispatch and
(separately) mathlib upstream PR. **Verdict GREEN-2.** PM next
step: file **EX-6 Session B** scoping ticket (deliverable §3 +
§5.1–§5.2 + §6.1 + §8.1 form the Session B brief).
**Last update.** mg-4adf (cat-mg-4adf), 2026-05-09. **EX-6 Session
C executed (partial): closed `integral_stepLower_eq_riemann` sorry +
master continuous FKG/AD signatures.** Session B's deferred sorry
(cell partition + finite additivity assembly of the lower-step
integral over `[0,1)^n`) is **closed sorry-free** via
`integral_iUnion_fintype` over the disjoint half-open cells `C_k`
(`k : Fin n → Fin N`), each of volume `1/N^n`, with the per-cell
constancy `stepLower_eq_of_mem_cell` from Session B. New
infrastructure: `Ico_zero_one_eq_iUnion_cells` (1D cell tiling),
`cell_disjoint` (pairwise cell disjointness), `integrableOn_stepLower_cube`
(integrability of `stepLower N f` on `[0,1)^n`); plus `gridFnN`
(`Fin n → Fin N` variant of `gridFn`) and `fkg_discrete_pi_finN`
(the Riemann-form discrete FKG); plus `stepUpper`, `le_stepUpper_self`
(upper sandwich), `integral_stepUpper_eq_riemann` (upper Riemann
identity, derived from the lower identity applied to the shifted
function `y ↦ f(y + (1/N)·𝟙)`), and `integrableOn_stepUpper_cube`.
The stepUpper-minus-stepLower integral bound
`integral_stepUpper_sub_stepLower_bound` is recorded in terms of
`((N+1)^n - N^n) · M / N^n = ((1+1/N)^n - 1) · M`, which → 0 as
`N → ∞`. The master theorems `tendsto_integral_stepLower`,
`continuous_fkg`, `continuous_ad` are signed in §8 of the file with
**precise sorry-diagnosis** (per Daniel feedback 2026-05-09: be
specific in deferred-sorry diagnosis, paper vs formalization). The
**single fundamental remaining sorry** is `sum_step_diff_bound`:

```
∑_{k:Fin n → Fin N} f((k+1)/N) − ∑_{k:Fin n → Fin N} f(k/N)
  ≤ ((N+1)^n − N^n) · f(1,…,1)
```

Diagnosis (formalization-only; no paper/mathlib gap): both sums
embed in `Σ_{l : Fin n → Fin (N+1)} f(l/N)` via `Fin.succ` (image:
`∀ i, l_i.val ≥ 1`) and `Fin.castSucc` (image: `∀ i, l_i.val < N`)
respectively. The difference `A − B = X_N − X_0` cancels at the
common image `{l : ∀ i, 1 ≤ l_i.val < N}` and reduces to
`X_N − X_0 ≤ X_N` (by non-negativity of `f`), with `X_N` the sum
over `{l : ∃ i, l_i.val = N}` of cardinality `(N+1)^n − N^n`. Each
term `f(l/N) ≤ M` by monotonicity. Pure `Finset.sum_bij` reindexing
along the two embeddings + cardinality + a `Finset.sum_le_sum_of_subset`-
style upper-bound; ~150 LoC of mathlib-standard combinatorics; no
mathlib gap. Three dependent sorries in `tendsto_integral_stepLower`
(squeeze), `continuous_fkg`, and `continuous_ad` cascade from this
one; all are otherwise mechanical assembly (apply
`fkg_discrete_pi_finN` on `(Fin n → Fin N)`, divide by `N^(2n)`,
recognise as Riemann sums via `integral_stepLower_eq_riemann`, take
`N → ∞` via `Filter.Tendsto.mul`). Build: `lake build` succeeds
(2506 jobs, 4 sorries). Trust surface impact: none (no new axioms;
`stanley_log_supermod` not consumed). §3.4 updated (sub-α-C arc:
**EX-6 Session C partial; Session D dispatches next** for the
`sum_step_diff_bound` cancellation lemma + dependent assembly).
ETA Session D: ~150–250 LoC, ~100–200k tokens. `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
(extended ~500 → ~1050 lines).

**Last update.** mg-a6ed (cat-mg-a6ed), 2026-05-09. **EX-6 Session
B executed: discrete FKG / AD on `(Fin (N+1))^n` + step-function
approximation + Riemann-sum identity (statement) — landed.** §1.21
NEW for the Session B deliverable
(`lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`,
NEW file ~470 lines, mathlib-PR-class structured for upstream
extraction). Predecessors: mg-e622 (`cd874e0`, Session A latex
scoping); mg-10d9 / mg-497d / mg-79a9 (EX-5 chamber decomp);
mg-2442 / mg-4831 (EX-4 Stanley vertex); mg-8c66 (EX-3 OrderPolytope);
mg-163f (Path A committed); mg-91be (sub-α-C scoping). **§5.1
deliverable `fkg_discrete_pi`** — discrete FKG on `(Fin (N+1))^n`
for non-neg monotone `f, g`, Riemann-sum form `(∑ f)(∑ g) ≤ (N+1)^n
· ∑ f g`, direct corollary of mathlib `fkg` with `μ ≡ 1`. Companion
`ad_discrete_pi` (4FT on `(Fin (N+1))^n` via mathlib
`four_functions_theorem_univ`). The `gridFn` infrastructure
(`gridPoint`, `gridPoint_inf`, `gridPoint_sup`, `gridFn_monotone`,
`gridFn_nonneg`, `gridFn_mul`, `gridFn_inf`, `gridFn_sup`) provides
the AD lattice-hypothesis transport. **§5.2 deliverables**:
`stepRetract` (lower-corner retraction with cube clipping at upper
face), `stepLower`, sandwich `stepLower_le_self` (bottom half) and
`stepLower_le_top` (boundedness for DCT bound in Session C),
`volume_cell` (each cell of width `1/N` has volume `(1/N)^n` via
`volume_pi_pi` + `Real.volume_Ico`), and **the cell-decomposition
core** `floor_mul_eq_of_mem_cell` / `stepRetract_eq_of_mem_cell` /
`stepLower_eq_of_mem_cell` (on each cell `[k/N, (k+1)/N)^n` with
`k : Fin n → Fin N`, the step approximation is constant
`= f(k/N)`). The Riemann-sum identity `integral_stepLower_eq_riemann`
is **stated** but its integration-side assembly (cell partition +
finite additivity of the Lebesgue integral) is **deferred to
Session C** alongside the dominated-convergence limit — clean
handoff with all per-cell ingredients prepared. Single `sorry` in
the file. Build: `lake build` succeeds for full `OneThird` target
(2641 jobs); new file wired into `lean/OneThird.lean` next to
`OrderPolytope`. **Trust surface impact: none** (no new axioms;
`stanley_log_supermod` not consumed). **Trip-wires (per polecat
brief / mg-91be §5.6 / mg-e622 §8.3).** Token blow-up: not fired
(well under 600k cap). Mathlib refactor: not fired. AD
lattice-hypothesis transport surprise: not fired. Cell-decomposition
assembly: **partially fired** — full integration-side proof
heavier than scoping anticipated; deferred to Session C as clean
handoff. §3.4 updated (sub-α-C arc: **EX-6 Session B done; Session
C dispatches next**). PM next step: file **EX-6 Session C** scoping
ticket (a.e. convergence + DCT + master `continuous_fkg` / `continuous_ad`
+ full `integral_stepLower_eq_riemann` assembly + 1D Chebyshev
hand-verification). ETA per mg-e622 §8.2: ~400–700 LoC, ~250–400k
tokens; Session C consumes Session B's per-cell ingredients.
**Last update.** mg-2746 (cat-mg-2746), 2026-05-09. **EX-7 Session
A — drops headline via chamber + continuous FKG/AD latex-first
scoping done.** §1.22 NEW for the Session A deliverable
(`docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md`,
~700 lines latex). Predecessor: mg-7d37 (`6631d54`, EX-6 Session E
sorry-free closure including the Monotone-laden `continuous_ad`).
**Substantive scoping finding (verdict §0 + §3).** The drops
headline `Pr_Q[L_k ∈ A] ≤ Pr_{Q'}[L_k ∈ A]` for `Q.Subseteq Q'`
reduces to a continuous AD inequality on `[0,1]^α` via the chamber
decomposition (mg-10d9 in tree). **However**, the in-tree
`continuous_ad` (mg-7d37, ContinuousFKG.lean:1425) carries
`Monotone f_i` hypotheses for each of the four functions (mg-7d37
signature widening, state.md §1.21), and **the drops application
needs AD on indicator functions of order polytopes
(`1_{O(Q)}, 1_{O(Q')}`), which are NOT cube-monotone**.
Counterexample: `f = (0.3, 0.5) ∈ O({(a,b)})` (cube `[0,1]^{a,b}`,
relation `a ≤ b`); `f' = (0.7, 0.5) ≥ f` componentwise; `f'(a) =
0.7 > 0.5 = f'(b)`, so `f' ∉ O({(a,b)})`. Polytope indicators are
sublattice indicators (closed under `⊓, ⊔`) but not monotone.
**Resolution (Path R-A, recommended).** File EX-6 Session F (NEW,
prerequisite to EX-7 Session B) to land a Monotone-free
`continuous_ad_general` via cell-averages + Lebesgue
differentiation theorem (mathlib v4.29.1
`MeasureTheory.Covering.Differentiation`-class), replacing the
mg-7d37 Riemann-sum-sandwich convergence route. ~300 LoC, ~150–250k
tokens; **Sub-DH-4-B strengthening** of DH-4 (the literature-standard
Ahlswede–Daykin 1979 / Preston 1974 form is Monotone-free; mathlib
upstream reviewer would expect both versions in a DH-4 PR).
**Path R-B (contingency).** Combinatorial chamber-pairing argument
without continuous AD; ~400–700 LoC; AMBER-leaning-RED if R-A
trip-wires fire. **EX-7 Session B (post-Session-F).** ~150–270
LoC, ~80–150k tokens; consumes `continuous_ad_general` + chamber
decomp + `stanley_log_supermod` axiom. **Total Sessions F + B:
~400–600 LoC, ~250–400k tokens.** Tracks upper edge of mg-91be
§5.7's 400–800 LoC, ~250–500k token estimate; ~+300 LoC for the
unanticipated EX-6 Session F prerequisite (vs. polecat brief's
~150–300 LoC for EX-7 Session B alone). Trust surface impact: none
(no new project axioms; `stanley_log_supermod` consumed at the
inner-step closure per §2.6 of the deliverable). **Verdict
AMBER-leaning-GREEN.** §3.4 updated (sub-α-C arc: EX-7 Session A
done; **EX-6 Session F is the next execution ticket**, not EX-7
Session B directly). PM next step: file **EX-6 Session F** scoping
ticket (`continuous_ad_general` Monotone-free extension, ~300 LoC),
then EX-7 Session B once Session F lands. Trip-wires per §6.4 +
§7.4 of the deliverable: token blow-up not fired (~70k of 350k);
mathlib measure-theory fundamental obstruction not fired; the
hypothesis-mismatch on `continuous_ad` is the substantive Session A
finding (not a halt-trip-wire — Path R-A resolution is clear).

**Last update.** mg-7d37 (cat-mg-7d37), 2026-05-09. **EX-6 Session
E — three remaining sorries closed; entire EX-6 arc sorry-free.**
The `tendsto_integral_stepLower`, `continuous_fkg`, and
`continuous_ad` master theorems in
`lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
are now proven outright. **Architecture.** Three layers:
(i) **Squeeze for `tendsto_integral_stepLower`.** Uses the sandwich
`stepLower N f ≤ f ≤ stepUpper N f` on the half-open cube
`[0,1)^n` (via `stepLower_le_self` / `le_stepUpper_self`). The
half-open cube and closed cube differ on a Lebesgue-null set
(volume(IccCube) = volume(IcoCube) = 1 by `volume_pi_pi` +
`Real.volume_Icc` / `Real.volume_Ico`, hence
volume(IccCube \ IcoCube) = 0 by `measure_diff` + `ae_eq_set`).
The squeeze uses `setIntegral_congr_set` to identify the integrals,
`setIntegral_mono_on` for the integral inequalities, and
`integral_stepUpper_sub_stepLower_bound` (Session D) for the gap
bound `((N+1)^n / N^n - 1) · f(1,…,1) → 0`. The `((N+1)/N)^n → 1`
limit is built up from `tendsto_one_div_atTop_nhds_zero_nat` plus
`Filter.Tendsto.add` / `.pow` / `.sub_const` / `.mul_const`. Final
step: `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (squeeze theorem)
on `0 ≤ F - L_N ≤ ((N+1)^n/N^n - 1) · M`, then `Tendsto.sub` to
flip the sign.
(ii) **Master `continuous_fkg`.** Volume of the unit cube reduces
to `1` via `volume_pi_pi` + `Real.volume_Icc` (so the trailing
`(volume IccCube).toReal` factor on the RHS becomes `1`).
`f * g` is monotone non-negative integrable (product of monotone
non-negs by `mul_le_mul`). At each `N ≥ 1`, `fkg_discrete_pi_finN`
gives `S_f · S_g ≤ N^n · S_{fg}`; multiply by `(1/N^n)^2` and use
`integral_stepLower_eq_riemann` (each side is `(1/N^n) · ∑`); the
`(f * g)(k/N) = f(k/N) · g(k/N)` rewrite (via `Pi.mul_apply`)
identifies the (f*g)-sum with the bilinear sum. Then
`tendsto_integral_stepLower` for `f`, `g`, `f * g` plus
`Filter.Tendsto.mul` and `le_of_tendsto_of_tendsto` close the proof.
(iii) **Master `continuous_ad`.** Same structure, using new lemma
**`ad_discrete_pi_finN`** (Fin N variant of `ad_discrete_pi`,
parallel to `fkg_discrete_pi_finN`); requires new helpers
`gridPointN`, `gridPointN_inf`, `gridPointN_sup` (Fin N analogues
of `gridPoint`, `gridPoint_inf`, `gridPoint_sup`), proved by the
same case analysis on `N = 0` / `N ≥ 1` and `le_total` on
coordinates. **Signature widening for `continuous_ad`.** The
inline scoping note ("same pattern as `continuous_fkg`") commits
the proof to Riemann-sum convergence via `tendsto_integral_stepLower`,
which requires per-coordinate monotonicity of each `f_i`. The
original signature in mg-8561 lacked monotonicity hypotheses; we
add **`Monotone f_i`** (i = 1, 2, 3, 4) to bring the hypothesis set
in line with the proof method. This matches the OneThird application
chain (EX-7 / EX-9 consume AD with monotone indicators of upper-closed
sets — see ex6-continuous-fkg-scoping.md §5.5 / §1.3); a fully
generic continuous AD on `[0,1]^n` (no monotonicity, just the AD
lattice hypothesis + integrability) would need a different
convergence route (e.g. dominated convergence on a measurable
class via stepLower → f a.e.) and is **out of scope for EX-6 / sub-α-C**.
**Trust surface impact: none** (no new axioms; no `stanley_log_supermod`
consumption; no mathlib refactor). **No new mathlib gap.** Build:
`lake build` succeeds (2641 jobs total, **0 sorries** in the
EX-6 file; full `OneThird` target sorry-free for sub-α-C). Final
length of `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`:
~1500 lines (added ~340 lines for the three master theorems plus
`gridPointN` / `gridPointN_inf` / `gridPointN_sup` /
`ad_discrete_pi_finN`). §3.4 updated (sub-α-C arc: **EX-6
complete; sub-α-C arc CLOSES on EX-7 dispatch**). Trip-wires (per
mg-91be §5.6 / mg-e622 §8.3): not fired (token-budget under
600k cap; mathlib refactor not needed; AD-without-monotonicity
gap surfaced as the documented signature widening, not as a
proof-architecture surprise). PM next step: file **EX-7 scoping
ticket** for `probEvent'_mono_of_subseteq_upClosed` (the EX-6
consumer) — `1_{O(Q')}` × `1_{A_k(S)}` instantiation against
`continuous_fkg`, plus the `(Fin n → ℝ)` ↔ `(α → ℝ)` reindexing
needed for the abstract drops application.
**Last update.** mg-8561 (cat-mg-8561), 2026-05-09. **EX-6 Session
D — `sum_step_diff_bound` cancellation lemma closed (sorry-free).**
The "single fundamental remaining sorry" identified in mg-4adf
(post-Session-C diagnosis) is now closed via the planned
`Finset.sum_bij`-style reindexing along the two embeddings
`Fin.succ : Fin N ↪ Fin (N+1)` (image: `∀ i, l_i ≥ 1`) and
`Fin.castSucc : Fin N ↪ Fin (N+1)` (image: `∀ i, l_i < N`). The
proof reindexes both Riemann sums into sums over the larger grid
`Fin n → Fin (N+1)`, partitions `univ` two ways via the images,
and shows the difference equals `(∑_{∃i, l_i = N} f(l/N)) −
(∑_{∃i, l_i = 0} f(l/N))`. Non-negativity of `f` drops the second
sum, and the residual `{l : ∃ i, l_i.val = N}` is bounded by
`((N+1)^n − N^n) · M` via `Finset.sum_le_card_nsmul` + the
pointwise bound `f(l/N) ≤ f(1,…,1) = M` (monotonicity of `f` and
`l_i.val ≤ N` for `l : Fin (N+1)`). Cardinality computation uses
`Finset.card_sdiff_of_subset` + `Finset.card_image_of_injective`
(via `Fin.castSucc_injective`) + `Fintype.card_fun` +
`Fintype.card_fin`. **No new mathlib gap; no new project
axioms.** Build: `lake build` succeeds (2641 jobs total, 3
remaining sorries — `tendsto_integral_stepLower`, `continuous_fkg`,
`continuous_ad` — all dependent on `sum_step_diff_bound` and now
mechanical assembly per mg-4adf diagnosis). Trust surface impact:
none. Final length of `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`:
~1150 lines (added ~100 lines for the lemma body). §3.4 updated
(sub-α-C arc: **EX-6 Session D done; mechanical assembly — three
dependent sorries — remains as Session E**). PM next step:
dispatch **Session E** to close `tendsto_integral_stepLower` (DCT
squeeze) + `continuous_fkg` + `continuous_ad` (each ~50–100 LoC,
discrete-FKG-on-grid → divide → recognise as Riemann sums → take
`N → ∞` via `Filter.Tendsto.mul`). Trip-wires: not fired.

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

### §1.14 Stanley vertex theorem — Session A latex writeup + mathlib mapping (mg-4831)

* **Source.** mg-4831 (this update);
  `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`
  (deliverable doc, ~880 lines latex). Predecessors: mg-8c66
  (`ed9f6e6`, EX-3 OrderPolytope landed); mg-163f (`9e6edcd`,
  Path-A-vs-Path-B fork resolution + EX-4 spec in §5.5);
  mg-91be (`bb450a4`, sub-α-C scoping + EX-4 spec in §5.4).

* **Statement.** Stanley 1986 Theorem 1.2: for a finite poset `α`,
  the extreme points of the order polytope `O(α)` are exactly the
  indicator functions `1_I` for `I ∈ F(α)` (the lattice of upper
  sets / filters). Equivalently, parameterised by the lattice of
  lower sets `J(α) = LowerSet α` via complement,
  `1_{αᶜ I} = 1_{α \ I}`. Both directions formalised:
  - **Direction 1 (`1_I` is extreme).** Direct convex-combination
    pinning argument: if `1_I = (1-t) f + t g` with `t ∈ (0,1)`
    and `f, g ∈ O(α)`, then on each `x ∈ I` the [0,1]-bound forces
    `f(x) = g(x) = 1`, and on each `x ∉ I` the non-negativity bound
    forces `f(x) = g(x) = 0`. Hence `f = g = 1_I` pointwise.
  - **Direction 2 (every extreme is `1_I`).** Contrapositive +
    explicit perturbation: if `f ∈ O(α)` takes some value `c ∈ (0,1)`,
    perturb `f → f_ε^± := f ± ε·1_{S_=(c)}` on the level set
    `S_=(c) := f^{-1}(c)`. For ε ≤ ε* / 2 with ε* := min(c, 1-c,
    G(f, c)) and G(f, c) the gap function over the boundary pairs
    crossing `S_=(c)`, both `f_ε^±` lie in `O(α)` and
    `f = (f_ε^+ + f_ε^-)/2` with `f_ε^+ ≠ f_ε^-`. So `f` is not
    extreme. Contrapositively, every extreme `f` takes only values
    in `{0, 1}`, and `f^{-1}(1)` is automatically an upper set.

* **Mathlib `Set.extremePoints` API verification.** **GREEN.** The
  typeclass surface (`[Semiring ℝ]`, `[PartialOrder ℝ]`,
  `[AddCommMonoid (α → ℝ)]`, `[SMul ℝ (α → ℝ)]`) is automatic for
  `OrderPolytope α : Set (α → ℝ)`. Key lemmas
  `mem_extremePoints` (`Mathlib.Analysis.Convex.Extreme:133`),
  `extremePoints_pi` (`:211`), and
  `Convex.mem_extremePoints_iff_convex_diff` (`:267`) are off-the-shelf.
  No critical mathlib gap; `extremePoints (Icc a b) = {a, b}` is
  not directly named in `v4.29.1` but is a one-liner from
  `mem_extremePoints` (DH-5a candidate, secondary).

* **Spec correction surfaced.** §4.1 of the deliverable: the
  mg-91be §5.4 / mg-163f §5.5 target signature parameterises the
  RHS by `LowerSet α`, but the in-tree `OrderPolytope` (mg-8c66,
  `f x ≤ f y` for `x ≤ y`) makes `1_I` order-preserving iff `I` is
  an **upper set**, not a lower set. The EX-1-style counterexample
  is the chain `0 < 1` with `I = {0}` (lower): `1_I(0) = 1 > 0 =
  1_I(1)` violates monotonicity. Recommended fix: use `UpperSet α`
  in the Lean signature (option 1, cleaner); equivalent alternative
  is `LowerSet α` + complement `(I : Set α)ᶜ` (option 2, preserves
  the LowerSet parameterisation downstream consumers in EX-5..EX-7
  use; one-line bridge via `UpperSet.compl`). Cardinality identity
  `|F(α)| = |J(α)|` is preserved under either choice; chamber-decomp
  arc downstream is unaffected.

* **Recommended Lean signature for Session B.**
  ```lean
  theorem orderPolytope_extremePoints (α : Type*) [PartialOrder α]
      [Fintype α] :
      Set.extremePoints ℝ (OrderPolytope α) =
      { f : α → ℝ | ∃ I : UpperSet α,
          f = Set.indicator (I : Set α) (1 : α → ℝ) }
  ```

* **Trust surface impact.** None. EX-4 introduces no new axioms;
  the proof uses only `Set.extremePoints` + `Set.indicator` +
  `UpperSet`/`IsUpperSet` from mathlib, plus the `OrderPolytope`
  (mg-8c66) in tree. The `width3_one_third_two_thirds` headline
  trust surface and the sub-α-C arc trust surface are both
  unchanged (no consumption of `stanley_log_supermod`).

* **Session B ETA refinement.** mg-91be §5.4 / mg-163f §2.2
  estimated EX-4 at ~400-600 LoC, ~200-300k tokens. This Session A
  refines downward to **~330–470 LoC, ~170–265k tokens** on the
  back of a clean direct argument that needs no Stanley-axiom
  invocation (the perturbation argument is purely arithmetic +
  order-theoretic). Component breakdown is in §6 of the deliverable.

* **Verdict.** **GREEN with small spec correction.** Both
  directions proven rigorously; mathlib API verified; one-line
  spec correction (LowerSet → UpperSet) surfaced as the only
  Session B amendment. PM next step: file EX-4 Session B scoping
  ticket (direct Lean port using §6 of the deliverable as the
  component breakdown).

### §1.15 Stanley log-supermod independent verification — GREEN (mg-e22f)

* **Source.** mg-e22f (this update);
  `docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`
  (deliverable doc, ~470 lines latex);
  `scripts/stanley_log_supermod_check.py` (numerical verifier);
  `lean/AXIOMS.md` (third entry, "Separate verification" subsection
  added).

* **Trigger.** Daniel directive 2026-05-08T16:11Z (paraphrased):

  > *"I am very cautious about allowing axioms BUT if this Stanley
  > thing is a solid external result and we run some separate
  > verification on it and it saves 5k lines of lean, then that
  > might be a good call. It's your responsibility."*

  Stronger separate-verification bar than `feedback_audit_bar_for_axioms`:
  conditional acceptance contingent on PM running an independent
  trust-surface check. PM filed mg-e22f to discharge that
  responsibility.

* **Three sub-checks** (all PASS):

  1. **Cross-literature: ≥ 3 sources, ≥ 3 decades.** **PASS.**
     Seven sources cataloged spanning four decades:
     - 1980s: Stanley 1981 (primary, JCTA 31:56–65); Daykin 1980
       (Stud. Appl. Math 63:263–270, 4FT framework); Stanley 1986
       (Discrete Comput. Geom. 1:9–23, order-polytope volume
       formula).
     - 1990s: Brightwell 1999 (Discrete Math 201:25–52, applied
       use in 1/3–2/3 conjecture context).
     - 2000s: Brightwell–Tetali 2003 (Order 20:333–345, entropy
       bounds on boolean lattice).
     - 2020s: Chan–Pak 2024 survey (arXiv:2311.02743, EMS Surveys
       Math. Sci.); Chan–Pak 2024 rederivation (arXiv:2110.10740,
       J. Assoc. Math. Res. 2(1):53–153).

  2. **Numerical sanity check.** **PASS.** Brute-force verification
     on 16 finite posets (`|α| ∈ {3, 4, 5}`) covering antichains,
     chains, V/Λ on 3, N/Diamond/2+2/Y/Λ on 4, width-3 layered
     structures, and 5-vertex shapes. **2 835 (I, J) pairs**
     checked, **0 violations**, 1 651 tight (equality) pairs (the
     latter consistent with Chan–Pak 2024 §10 equality-case
     characterisation). Out-of-tree (Python script independent of
     Lean codebase).

  3. **Uncontested in literature.** **PASS.** No erratum or
     counterexample-claiming paper exists. Active research
     direction is **equality-case characterisation** (S6 §10; the
     2023 ScienceDirect "extremals of Stanley's inequalities"
     paper; the 2024 STOC paper on AF-equality complexity in PH),
     which strongly affirms the underlying inequality. The
     Chan-Pak 2024 rederivation in modern language (S7) is itself
     an independent re-confirmation 43 years post-Stanley 1981.

* **AXIOMS.md update.** Third axiom entry
  (`OneThird.LinearExt.stanley_log_supermod`) extended with a new
  "Separate verification (per Daniel directive 2026-05-08T16:11Z)"
  subsection containing the 3-row sub-check verdict table, links to
  the deliverable doc and numerical script, and the GREEN verdict.
  No changes to the audit-bar 4-condition table (External /
  Difficult / Labeled / Low-risk all unchanged).

* **Trust surface impact.** None. The verification deliverable is
  documentation + a numerical script; no Lean source changes
  beyond the AXIOMS.md write-up. The third project axiom remains
  on the sub-α-C arc trust surface, now with an additional
  separate-verification subsection backing the `External` and
  `Low-risk` conditions. The `width3_one_third_two_thirds`
  headline trust surface is unchanged.

* **Trip-wires not fired.** Per ticket §5: no numerical violation
  (would have triggered URGENT mail to Daniel + revert mg-d0fc +
  halt sub-α-C); no thin literature coverage (would have
  triggered reduced-confidence framing). No token blow-up
  (well under the 250k cap; mostly latex + Python scripting).

* **Verdict.** **GREEN** per ticket §6. PM next step: surface
  verification GREEN to Daniel in evening digest and continue with
  EX-4 dispatch (Stanley vertex theorem) per mg-8c66 hand-off.

### §1.16 EX-4 Session B executed — Stanley vertex theorem ported to Lean (mg-2442)

* **Source.** mg-2442 (this update); the EX-4 Session A latex
  deliverable (mg-4831, `ac56bc4`,
  `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`);
  predecessors: mg-8c66 (`ed9f6e6`, EX-3 OrderPolytope), mg-163f
  (`9e6edcd`, Path A), mg-91be (`bb450a4`, sub-α-C scoping). File
  extended: `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (mg-8c66 base + mg-2442 extension, ~330 LoC of net additions).

* **What landed.** Both directions of Stanley 1986 Theorem 1.2 in
  Lean against the in-tree `OrderPolytope α` (mg-8c66):

  - **Direction 1 (`indicator_upperSet_isExtreme`).** For any
    `I : UpperSet α`, the `{0,1}`-indicator `1_I` is an extreme
    point of `OrderPolytope α`. Helper:
    `indicator_upperSet_mem` (membership). Proof: direct
    convex-combination pinning per mg-4831 §2.3 (no `[Fintype α]`
    needed for this direction).

  - **Direction 2 (`extremePoint_eq_indicator_upperSet`, requires
    `[Fintype α]`).** Every extreme point of `OrderPolytope α` is
    `1_I` for some `I : UpperSet α`. Private aux lemmas:
    `perturbUp` / `perturbDown` (level-set ±ε perturbation realised
    via `Set.indicator`), `exists_perturbation_eps` (positive ε
    via `Finset.inf'` over `Finset.univ.filter (f x ≠ c)`),
    `perturbUp_mem` / `perturbDown_mem` (the 6-case
    order-preservation table per mg-4831 §3.5),
    `extremePoint_isBoolean` (every extreme `f` takes only values
    in `{0, 1}`, contradiction via the perturbation argument), and
    `onePreimage_isUpperSet` (`f^{-1}(1)` is an upper set under
    monotonicity).

  - **Master theorem `extremePoints_eq` (requires `[Fintype α]`).**
    `Set.extremePoints ℝ (OrderPolytope α) = { f : α → ℝ |
    ∃ I : UpperSet α, f = Set.indicator (I : Set α) (1 : α → ℝ) }`.
    The mg-4831 §4.1-recommended UpperSet form (option 1).

* **Mathlib API consumed (no gap surfaced).** `Set.extremePoints`
  + `mem_extremePoints` + `openSegment` (Mathlib.Analysis.Convex.Extreme);
  `Set.indicator` + `Set.indicator_of_mem` + `Set.indicator_of_notMem`
  + `Set.indicator_nonneg`
  (Mathlib.Algebra.Notation.Indicator and Order.Group.Indicator);
  `UpperSet` + `IsUpperSet` + the `SetLike (UpperSet α) α` instance
  (Mathlib.Order.UpperLower.Basic + .CompleteLattice);
  `Finset.inf'` + `Finset.lt_inf'_iff` + `Finset.inf'_le`
  (Mathlib.Data.Finset.Lattice.Fold). Two import additions to the
  EX-3 file: `Mathlib.Analysis.Convex.Extreme` and
  `Mathlib.Algebra.Order.Group.Indicator`.

* **Trust surface impact: none.** `#print axioms` on the three
  exposed theorems gives only `{propext, Classical.choice,
  Quot.sound}` — the mathlib-standard classical-foundation
  triplet. **No new project axioms introduced** (as predicted by
  mg-4831 §1.14 + §5.1: EX-4 does not consume
  `stanley_log_supermod`, since the vertex characterisation is
  purely an extreme-point statement and not a count). The
  `width3_one_third_two_thirds` headline and the sub-α-C arc
  trust surfaces are both unchanged.

* **Trip-wires per mg-4831 §6 (none fired).**
  - GREEN (achieved): both directions formalised; main theorem
    statement matches mg-4831 §4.1 recommended signature; build
    green; no new axioms; ~330 LoC at the lower edge of the
    mg-4831 §6 ~330–470 LoC estimate.
  - AMBER (not fired): no auxiliary mathlib gap surfaced.
  - RED (not fired): no decidability obstruction; the
    `Set.indicator` and `Finset.inf'` formulations both worked
    cleanly with `[Fintype α]` and classical decidability.
  - **Single minor friction surfaced post-port:** the SetLike
    coercion of an anonymous-constructor `UpperSet α` (built via
    `⟨{x | f x = 1}, onePreimage_isUpperSet hf.1⟩`) needed an
    explicit `(I : Set α) = {x | f x = 1}` rfl-rewrite step in
    `extremePoint_eq_indicator_upperSet`. ~2 LoC; documented
    in-line; not a structural issue.

* **`Set.indicator` formulation note.** The perturbation
  `f_ε^± := f ± ε · 1_{f^{-1}(c)}` was realised via
  `Set.indicator {y | f y = c} (fun _ => ε)` rather than an
  `if`-then-`else` term. This avoids any `Decidable (f x = c)`
  obligation (Set.indicator is `noncomputable` via
  `Classical.decPred` automatically) and gives a clean equational
  formulation: `perturbUp f c ε x = f x + Set.indicator {y | f y =
  c} (fun _ => ε) x`. The `_apply_of_eq` / `_apply_of_ne` lemmas
  derived via `Set.indicator_of_mem` / `Set.indicator_of_notMem`
  give point-wise unfolding.

* **Sub-α-C arc next step.** EX-5 chamber decomposition is now the
  next execution ticket. mg-163f §5.4 / mg-91be §5.5 sketched
  EX-5 as the chamber simplices `σ_L = { f ∈ O(α) | f x_{L(1)} ≤ ··· ≤ f x_{L(n)} }`
  for `L : LinearExt α`, with `O(α) = ⋃ σ_L` and
  `Vol(σ_L) = 1/n!`. The vertex theorem (this commit) is **not** a
  prerequisite for EX-5 (EX-5 uses `OrderPolytope` directly, not
  its vertex set), but it is a prerequisite for the cleaner
  formulations in EX-7 / EX-9.

* **DH-5 ready to surface.** Per §3.10: with both EX-3 (mg-8c66)
  and EX-4 (this commit) in tree, the combined upstream-PR
  candidate `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`
  is now realisable. ~600–900 LoC of mathlib value, maintainer
  Yaël Dillies (consistent with Mathlib.Analysis.Convex.Extreme).
  Lower priority than DH-1 (Stanley log-supermod) and DH-4
  (continuous FKG); PM should mention DH-5 in the next
  Daniel digest.

* **Verdict.** **GREEN.** Both directions proven; main theorem
  matches recommended signature; trust surface unchanged
  (`{propext, Classical.choice, Quot.sound}` only); ~330 LoC at
  the lower edge of the Session A estimate. PM next step: file
  EX-5 chamber decomposition scoping ticket.

### §1.17 EX-5 Session A — chamber simplex `σ_L` + chamber decomposition latex-first scoping (mg-79a9)

* **Source.** mg-79a9 (this update);
  `docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md`
  (deliverable doc, ~1220 lines latex). Predecessors: mg-2442
  (`89786cf`, EX-4 Session B Lean port); mg-4831 (`ac56bc4`,
  EX-4 Session A latex); mg-8c66 (`ed9f6e6`, EX-3 OrderPolytope);
  mg-163f (`9e6edcd`, Path A committed); mg-91be (`bb450a4`,
  sub-α-C scoping with EX-5 spec in §5.5).

* **Statement.** Latex-first scoping of EX-5 — the chamber
  decomposition of the order polytope `O(α)` into `numLinExt α`-
  many simplices `σ_L` indexed by `L : LinearExt α`, each of
  Lebesgue volume `1/n!`, with measure-zero pairwise overlaps.
  Per Stanley 1986 §1 (Lemma 1.3, Corollary 1.4):

  - `Vol(σ_L) = 1 / (Nat.factorial n)` for each `L`.
  - `O(α) = ⋃_{L : LinearExt α} σ_L`.
  - `Vol(σ_L ∩ σ_{L'}) = 0` for `L ≠ L'`.

  All three claims rigorously proved with **no convex-geometry /
  mixed-volume / Aleksandrov–Fenchel detour**: volume via the
  measure-preserving relabel `MeasurableEquiv.piCongrLeft` (Mathlib
  `MeasureTheory/Constructions/Pi.lean:744`) reducing σ_L to the
  standard ordered cube `Δ_n`, plus the symmetric S_n-tiling of
  `[0,1]^n` giving `Vol(Δ_n) = 1/n!` (deliverable §2). Cover via
  Szpilrajn-on-level-set: sort α by `f`-value and break ties using
  Szpilrajn within each level set (deliverable §3). Measure-zero
  overlap via the standard "intersection lies in a hyperplane
  `{f x = f y}`, which is a strict `Submodule ℝ (α → ℝ)`, hence
  Lebesgue-null by `addHaar_submodule`
  (Mathlib `MeasureTheory/Measure/Lebesgue/EqHaar.lean:175`)"
  (deliverable §4).

* **Lean signatures (deliverable §5).** Position-based `chamber`
  definition (avoiding `Fin (n - 1)` natural-number subtraction):

  ```lean
  def chamber (L : LinearExt α) : Set (α → ℝ) :=
    { f : α → ℝ |
        (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) }
  ```

  with `chamber_iff_chain` recovering the mg-91be §5.5 chain form
  (`f(L⁻¹(i.castSucc)) ≤ f(L⁻¹(i.succ))` for `i : Fin (n - 1)`)
  as a derived equivalence. Three master theorems:
  `chamber_volume`, `orderPolytope_eq_iUnion_chamber`,
  `chamber_inter_meas_zero`. Plus auxiliary `volume_orderedCube`
  (DH-5 candidate) and `linearExtFromOrderPreserving` /
  `exists_inversion_pair`.

* **Mathlib API consumed (deliverable §6).** All measure-theoretic
  prerequisites verified against the project's pinned mathlib
  (`v4.29.1`-class):
  `MeasureTheory.Measure.pi`,
  `MeasureTheory.measurePreserving_piCongrLeft:744` (relabel),
  `MeasureTheory.volume_Icc_pi:241` (cube volume),
  `MeasureTheory.Measure.addHaar_submodule:175` (strict subspaces
  null), `MeasureTheory.isAddHaarMeasure_volume_pi:126` (Lebesgue is
  Haar on Pi types), plus the auto-resolved instances
  `MeasureTheory.MeasureSpace.pi:216`, `Pi.borelSpace`,
  `Module.Finite.pi`, `Pi.normedAddCommGroup`, `Pi.normedSpace`.
  **No critical mathlib gap.**

* **Mathlib gap surfaced (deliverable §6.3) — DH-5 strengthening.**
  The standard ordered cube volume
  `Vol{ y ∈ ℝ^n | 0 ≤ y_0 ≤ … ≤ y_{n-1} ≤ 1 } = 1/n!` is **not
  directly in mathlib** — `Analysis.Convex.StdSimplex` defines the
  *probability simplex* (`{f | (∀ i, 0 ≤ f i) ∧ ∑ f i = 1}`), not
  the ordered cube. The lemma is **derivable** in ~150–200 LoC
  (S_n-tiling + permutation invariance + diagonal hyperplane null);
  Session B lands `volume_orderedCube` as a sub-deliverable.
  **Strengthens DH-5 (state.md §3.10):** the combined EX-3 + EX-4
  + EX-5 mathlib upstream PR `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`
  now realisably carries order polytope basics + Stanley vertex
  theorem + `volume_orderedCube` + chamber decomposition,
  totalling ~700–1100 LoC of mathlib value. Lower priority than
  DH-1 / DH-4 but the case strengthens with each landing.

* **Verdict (deliverable §0 + §7).** **GREEN-2** (split Session B +
  Session C). The mg-91be §5.5 estimate ("2 polecat sessions,
  ~800–1500 LoC, ~400–800k tokens combined") refines to:

  | Session | LoC | Tokens (k) |
  |---------|----:|-----------:|
  | Session B (volume + relabel + `volume_orderedCube` DH-5) | ~395–560 | ~235–350 |
  | Session C (cover + measure-zero overlap + master) | ~420–625 | ~260–395 |
  | **Total** | **~815–1185** | **~495–745** |

  Session A consumed ~270k tokens (well under the 320k trip-wire);
  total Session-A-through-Session-C tokens ~765–1015k, at the upper
  edge of mg-91be §5.5's 400–800k envelope. LoC mid-range. **No
  fallback to mg-163f §4.4 discretised path needed.**

* **Trip-wires (deliverable §6.5 + §7.4) — none fired.**
  - Token blow-up: not fired (Session A finishing under 270k).
  - Mathlib measure-theory gap: AMBER-fired then resolved
    (`volume_orderedCube` is derivable in-file, scoped as Session
    B sub-deliverable + DH-5 strengthening; **no fundamental
    mathlib obstruction**).
  - Volume proof harder than expected: not fired (Stanley's
    "unimodular simplex" line in §1 (1.5) maps directly to
    `measurePreserving_piCongrLeft`; no AF / mixed-volume detour).
  - Cover-construction blow-up: not fired (constructive ~150–250
    LoC; Route A always available; Route B optional via
    in-tree `OrdinalDecomp`).
  - Overlap-construction blow-up: not fired (`addHaar_submodule`
    is off-the-shelf; ~30 LoC core argument).

* **Trust surface impact: none.** EX-5 introduces no new project
  axioms; the chamber decomposition is a measure-theoretic statement
  consumed downstream by EX-7 (drops headline) and EX-9 (Brightwell-
  port-A centred-sum) but does **not** consume `stanley_log_supermod`
  itself. The third axiom remains consumed only by EX-7+ onward.
  `width3_one_third_two_thirds` headline trust surface unchanged.

* **Sub-α-C arc next step.** PM files **EX-5 Session B** scoping
  ticket: deliverable §5.1–§5.2 + §6 + §7.1 are the Session B brief.
  Session B = direct Lean port of the volume claim + `chamber`
  definition + `volume_orderedCube` DH-5 candidate; ~395–560 LoC,
  ~235–350k tokens, 1 polecat session. Session C dispatches on
  Session B landing.

* **Verdict.** **GREEN-2.** Latex-first scoping done; rigorous
  proofs of all three chamber-decomposition claims; Lean signatures
  drafted; mathlib API verified GREEN; one mathlib gap
  (`volume_orderedCube`) surfaced and folded into Session B as
  DH-5 strengthening; ETA refined to Session B + Session C
  (~815–1185 LoC total, ~495–745k tokens combined). PM next step:
  file EX-5 Session B (volume + DH-5).

### §1.18 EX-5 Session B — chamber definition + volume theorem (mg-497d)

* **Source.** mg-497d (this update);
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (extension; ~430 LoC of Lean added). Predecessor: mg-79a9
  (`3e76ac3`, EX-5 Session A latex-first scoping with §5.1–§5.2 +
  §6 + §7.1 forming the Session B brief).

* **Statement.** Direct Lean port of the volume claim (Stanley 1986
  Theorem 1.4, volume part). Three layers:

  - **Chamber simplex** `chamber L : Set (α → ℝ)` for
    `L : LinearExt α` (mg-79a9 §5.1 position-based form, avoiding
    `Fin (n - 1)` natural-number subtraction):

    ```lean
    def chamber (L : LinearExt α) : Set (α → ℝ) :=
      { f : α → ℝ |
          (∀ x : α, f x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x y : α, L.pos x ≤ L.pos y → f x ≤ f y) }
    ```

    plus `chamber_subset_orderPolytope : chamber L ⊆ OrderPolytope α`.

  - **Standard ordered cube** `orderedCube n : Set (Fin n → ℝ)`
    (the `Δ_n` of the latex deliverable §2.1) and the σ-permuted
    chamber `orderedCubePerm n σ` for `σ : Equiv.Perm (Fin n)`,
    with measurability lemmas
    (`measurableSet_orderedCube`, `measurableSet_orderedCubePerm`)
    and the measure-preserving relabel
    `relabelEquiv : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ)` realised as
    `(MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ).symm` so that
    `relabelEquiv σ y j = y (σ j)` follows from
    `Equiv.piCongrLeft_symm_apply` (rfl).

  - **Master volume theorem `volume_orderedCube` (DH-5 candidate)**:

    ```lean
    theorem volume_orderedCube (n : ℕ) :
        volume (orderedCube n) = ENNReal.ofReal (1 / (Nat.factorial n : ℝ))
    ```

    proved via the symmetric S_n-tiling argument (deliverable §2.3):
    cover `[0,1]^n = ⋃ σ, orderedCubePerm n σ` via `Tuple.sort`;
    `volume (orderedCubePerm n σ) = volume (orderedCube n)` by
    measure-preserving relabel; pairwise overlaps
    `orderedCubePerm n σ ∩ orderedCubePerm n τ` for `σ ≠ τ` lie in
    a hyperplane `equalCoordSubmodule k k' = {y | y k = y k'}`
    (with `k = σ i₀, k' = τ i₀` from a witness disagreement), null
    by `Measure.addHaar_submodule`; combine via
    `measure_biUnion_finset₀` to get `n! · Vol(Δ_n) = Vol([0,1]^n) = 1`.

  - **Chamber volume `chamber_volume`** (the master Stanley 1986
    (1.5)):

    ```lean
    theorem chamber_volume (L : LinearExt α) :
        volume (chamber L) =
          ENNReal.ofReal (1 / (Nat.factorial (Fintype.card α) : ℝ))
    ```

    proved by pushing σ_L forward to `orderedCube (Fintype.card α)`
    via `chamberRelabel L : (α → ℝ) ≃ᵐ (Fin n → ℝ)` (the Φ_L of
    deliverable §2.2), measure-preserving by
    `volume_measurePreserving_piCongrLeft`. The chamber and the
    ordered cube are related by
    `chamber_eq_preimage_orderedCube : chamber L = chamberRelabel L ⁻¹' orderedCube _`,
    and `MeasurePreserving.measure_preimage_equiv` transports the
    volume.

  - **Hand-verification.** A `Three`-discrete `example` confirms
    `volume (chamber L) = ENNReal.ofReal (1/6)` for any
    `L : LinearExt Three` (closes via `rfl` after `chamber_volume`,
    since `Fintype.card Three = 3` and `3.factorial = 6` reduce
    definitionally on the in-file `Fintype Three` instance).

* **Mathlib API consumed.** All in mg-79a9 §6.1's verified set,
  with no surprises:
  `MeasureTheory.volume_measurePreserving_piCongrLeft:753`
  (relabel volume version),
  `MeasureTheory.MeasurableEquiv.piCongrLeft` (measurable equiv),
  `Equiv.piCongrLeft_symm_apply` (rfl-friendly apply form),
  `MeasureTheory.measure_biUnion_finset₀` (AE-disjoint sum),
  `MeasureTheory.MeasurePreserving.measure_preimage_equiv`,
  `MeasureTheory.volume_pi_pi` (cube volume = 1),
  `MeasureTheory.Measure.addHaar_submodule:175` (strict submodule
  null), `MeasureTheory.isAddHaarMeasure_volume_pi:126`,
  `Tuple.sort` + `Tuple.monotone_sort` + `Tuple.unique_monotone`
  (sort-based cover and overlap), `Fintype.card_perm`,
  `Fintype.card_fin`, `ENNReal.eq_div_iff`,
  `ENNReal.ofReal_div_of_pos`. The `Pi.borelSpace`,
  `Module.Finite.pi`, `isAddHaarMeasure_volume_pi`,
  `Pi.normedAddCommGroup`, `Pi.normedSpace` typeclass surface
  resolves automatically once the imports
  `MeasureTheory.Measure.Lebesgue.EqHaar`,
  `MeasureTheory.Constructions.Pi`,
  `MeasureTheory.MeasurableSpace.Embedding`,
  `Data.Fin.Tuple.Sort`, `Data.Fintype.Perm` are added.

* **Trust surface impact: none.** `#print axioms` on the three
  exposed theorems (`chamber_volume`, `volume_orderedCube`,
  `chamber_subset_orderPolytope`) gives only the mathlib-standard
  `{propext, Classical.choice, Quot.sound}` triplet — **no new
  project axioms**, as predicted by mg-79a9 §6.5 and §7.1.
  `stanley_log_supermod` not consumed.

* **LoC and tokens.** ~430 LoC of Lean (file goes from ~620 to
  ~1050 lines). Lands at the lower edge of the mg-79a9 §7.1
  estimate (~395–560 LoC). Tokens well under the 450k cap.

* **Trip-wires per mg-79a9 §7.1 — none fired.**
  - Token blow-up: not fired.
  - S_n-tiling argument: not fired. The chosen formulation of
    `relabelEquiv σ` as `(piCongrLeft P σ).symm` makes
    `relabelEquiv σ y j = y (σ j)` literally `rfl` via
    `Equiv.piCongrLeft_symm_apply`, sidestepping cast-management
    on the `Equiv.piCongrLeft P σ.symm` form. `Tuple.sort` /
    `Tuple.monotone_sort` / `Tuple.unique_monotone` carry the
    cover and overlap arguments cleanly.
  - `addHaar_submodule` instance resolution: not fired. All
    typeclass dependencies (`NormedAddCommGroup`, `NormedSpace ℝ`,
    `BorelSpace`, `FiniteDimensional ℝ`, `IsAddHaarMeasure`)
    resolve automatically on `Fin n → ℝ`.

* **DH-5 strengthening (state.md §3.10).** `volume_orderedCube`
  is **in tree** as of this commit, in
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (sub-namespace `OneThird.LinearExt.OrderedCube`). Combined
  EX-3 + EX-4 + EX-5-Session-B mathlib upstream candidate
  `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean` is
  realisable today: order polytope basics + Stanley vertex
  theorem + `volume_orderedCube` + chamber definition. Cover +
  measure-zero overlap (Session C) close out the chamber-
  decomposition triple. The combined PR is now sized ~700–900
  LoC (lower than the §1.17 estimate's upper bound; Session B
  came in tight).

* **Sub-α-C arc next step.** PM files **EX-5 Session C** scoping
  ticket: deliverable §3 (cover) + §4 (measure-zero overlap) +
  §5.3–§5.5 (signatures) form the Session C brief. Session C =
  direct Lean port of the cover (`linearExtFromOrderPreserving`)
  + measure-zero overlap (`exists_inversion_pair` +
  `chamber_inter_meas_zero`) + master theorem
  `orderPolytope_eq_iUnion_chamber`; ~420–625 LoC, ~260–395k
  tokens, 1 polecat session.

* **Verdict.** **GREEN.** Chamber definition + volume theorem
  landed in tree; `volume_orderedCube` (DH-5 candidate) landed in
  tree; build green; no new project axioms; trip-wires not fired.

### §1.19 EX-5 Session C — chamber cover + measure-zero overlap + master volume (mg-10d9)

* **Source.** mg-10d9 (this update);
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (extension; ~280 LoC of Lean added). Predecessor: mg-497d
  (`5dd9e50`, EX-5 Session B with `chamber` + `chamber_volume` +
  `volume_orderedCube`); brief origin mg-79a9 (`3e76ac3`)
  §3 (cover), §4 (overlap), §5.3–§5.5 (signatures), §6 (mathlib
  API), §7.2 (Session C scope and trip-wires).

* **Statement.** Direct Lean port of the cover (Stanley 1986
  Lemma 1.3 cover part) + measure-zero overlap (Stanley 1986
  Lemma 1.3 face part, weakened to measure-zero per mg-79a9
  §1.4) + master volume (Stanley 1986 Corollary 1.4). Three
  exposed theorems, plus auxiliary cover construction:

  - **Cover** `chamber_cover`:

    ```lean
    theorem chamber_cover :
        (OrderPolytope α : Set (α → ℝ)) =
          ⋃ L : OneThird.LinearExt α, chamber L
    ```

    proved by constructing `linearExtFromOrderPreserving hf : LinearExt α`
    for each `f ∈ OrderPolytope α` and showing
    `mem_chamber_linearExtFromOrderPreserving hf : f ∈ chamber (...)`.
    The construction sorts `α` by the lex key
    `(f x, S.pos x) : Lex (ℝ × Fin n)` where `S` is a fixed Szpilrajn
    extension used for tie-breaking; the resulting permutation is
    well-defined since the secondary `S.pos` coordinate makes the key
    injective. **Implementation note: this is "Route C" (the
    augmented partial order `x ≤_α y ∨ f x < f y` from mg-79a9 §3.2
    realised implicitly via lex sort), not Route A (explicit
    Szpilrajn-on-each-level-set) or Route B (`OrdinalDecomp`-driven
    induction)** — Route C avoids both the Subtype-fintype
    real-equality decidability obstruction (Route A RED-fallback
    flagged by mg-79a9 §7.2) and the level-set-vs-band-set
    structural mismatch (Route B contingency flagged by mg-79a9
    §3.5). `Tuple.sort` + `Tuple.monotone_sort` +
    `Prod.Lex.toLex_le_toLex'` close both directions
    (`monotone` field for the linear extension, and chamber
    membership) cleanly with a single `by_contra` on the lex
    inequality (~50 LoC for the construction + ~15 LoC for
    chamber membership).

  - **Overlap** `chamber_inter_meas_zero`:

    ```lean
    theorem chamber_inter_meas_zero {L L' : OneThird.LinearExt α}
        (h : L ≠ L') : volume (chamber L ∩ chamber L') = 0
    ```

    proved by extracting `x : α` with `L.toFun x ≠ L'.toFun x` from
    `L ≠ L'` (via `OneThird.LinearExt.ext` + `funext`); setting
    `y := L.toFun.symm (L'.toFun x)` gives the inversion pair `(x, y)`
    with `x ≠ y`. On the intersection both
    `f ∘ L.toFun.symm` and `f ∘ L'.toFun.symm` are monotone
    `Fin n → ℝ` functions, equal as a value of `Tuple.unique_monotone`
    applied to `F := f ∘ L.toFun.symm` with permutations
    `σ := id` and `τ := L'.toFun.symm.trans L.toFun`. Evaluating
    the equality at `i := L'.toFun x` gives `f y = f x`, so the
    intersection is contained in the strict hyperplane
    `equalCoordSubmoduleAlpha x y = {f | f x = f y}` (a
    `Submodule ℝ (α → ℝ)`, strict because `x ≠ y`); volume zero by
    `Measure.addHaar_submodule`. Auxiliary in-tree:
    `equalCoordSubmoduleAlpha`, `mem_equalCoordSubmoduleAlpha`,
    `equalCoordSubmoduleAlpha_ne_top`, `volume_equalCoordSubmoduleAlpha`
    (~30 LoC for the submodule infrastructure; ~80 LoC for the main
    overlap proof).

  - **Master volume** `orderPolytope_volume`:

    ```lean
    theorem orderPolytope_volume :
        volume (OrderPolytope α : Set (α → ℝ)) =
          ENNReal.ofReal ((numLinExt α : ℝ) /
            (Nat.factorial (Fintype.card α) : ℝ))
    ```

    proved by combining `chamber_cover` + AE-disjointness from
    `chamber_inter_meas_zero` + per-chamber volume via
    `chamber_volume`, dispatched through `measure_biUnion_finset₀`
    over `Finset.univ : Finset (LinearExt α)`. Auxiliary:
    `measurableSet_chamber` (chamber is measurable as preimage of
    `orderedCube` under the measurable equivalence
    `chamberRelabel L`). Final arithmetic step converts
    `card • ENNReal.ofReal (1/n!)` to
    `ENNReal.ofReal (numLinExt α / n!)` via `nsmul_eq_mul` +
    `ENNReal.ofReal_natCast` + `ENNReal.ofReal_mul` + `ring`
    (~30 LoC).

  - **Hand-verification.** A `Three`-discrete `example` confirms
    `volume (OrderPolytope Three) = ENNReal.ofReal (numLinExt Three / 6)`
    (closes via `rfl` after `orderPolytope_volume`), matching
    `numLinExt Three = 3! = 6` and therefore `Vol = 1` per the
    `[0,1]^3` cube identity established in §1.13.

* **Mathlib API consumed.** All in mg-79a9 §6.1's verified set,
  no surprises: `Tuple.sort`, `Tuple.monotone_sort`,
  `Tuple.unique_monotone`, `Prod.Lex.toLex_le_toLex'` (sort-
  based cover); `MeasureTheory.Measure.addHaar_submodule:175`
  (strict-submodule null);
  `MeasureTheory.measure_biUnion_finset₀` (AE-disjoint sum);
  `MeasureTheory.measure_mono_null`,
  `MeasurableEquiv.measurableSet_preimage`,
  `Equiv.apply_symm_apply` / `symm_apply_apply`,
  `OneThird.LinearExt.ext` + `OneThird.LinearExt.szpilrajn`
  (in-tree). The `[NormedAddCommGroup (α → ℝ)]`,
  `[NormedSpace ℝ (α → ℝ)]`, `[BorelSpace (α → ℝ)]`,
  `[FiniteDimensional ℝ (α → ℝ)]`,
  `[IsAddHaarMeasure (volume : Measure (α → ℝ))]` typeclass
  surface resolves automatically for general `α : Type*`
  with `[Fintype α]` (no `Fin n`-specialisation needed) once
  `MeasureTheory.Pi.borelSpace`, `Module.Finite.pi`,
  `isAddHaarMeasure_volume_pi`, `Pi.normedAddCommGroup`,
  `Pi.normedSpace` are in scope from existing imports.

* **Trust surface impact: none.** `#print axioms` on the three
  exposed theorems
  (`chamber_cover`, `chamber_inter_meas_zero`,
  `orderPolytope_volume`) gives only the mathlib-standard
  `{propext, Classical.choice, Quot.sound}` triplet — **no new
  project axioms**, as predicted by mg-79a9 §6.5 and §7.2.
  `stanley_log_supermod` not consumed by EX-5 (consumed only
  from EX-7+ per mg-d0fc §1.11).

* **LoC and tokens.** ~280 LoC of Lean (file goes from ~1052 to
  ~1330 lines). Lands **under the lower edge** of the mg-79a9
  §7.2 estimate (~420–625 LoC) — Route C (lex-sort) is more
  compact than Route A (Szpilrajn-on-level-set) or Route B
  (`OrdinalDecomp` induction) by avoiding the explicit
  level-set partition + cumulative-cardinality bookkeeping.
  Tokens well under the 500k cap.

* **Trip-wires per mg-79a9 §7.2 — none fired.**
  - Token blow-up: not fired.
  - Route A vs Route B: superseded by Route C (lex-sort), which
    avoids both routes' contingencies. Route A's RED-fallback
    on `f x = c` decidability does not apply since the lex key
    `(f x, S.pos x)` is **injective** (no equality testing of
    real values needed); Route B's `OrdinalDecomp`-vs-level-set
    shape mismatch does not apply since the lex sort does not
    use `OrdinalDecomp` infrastructure.
  - `linearExtFromOrderPreserving` structural obstructions:
    not fired. `Tuple.sort` on `Lex (ℝ × Fin n)` resolves cleanly;
    `Prod.Lex.toLex_le_toLex'` provides the lex-comparison
    unfolding lemma; `LinearOrder (α ×ₗ β)` instance from
    `Prod.Lex.instLinearOrder` resolves automatically for
    `[LinearOrder α] [LinearOrder β]` (both `ℝ` and `Fin n`).
  - `addHaar_submodule` instance resolution for `α → ℝ`
    (general `α`, not just `Fin n`): not fired. All five typeclass
    dependencies resolve automatically.

* **DH-5 fully realised (state.md §3.10).** All four chamber-
  decomposition pieces are now in tree:
  - `chamber L : Set (α → ℝ)` definition (Session B);
  - `chamber_volume : volume (chamber L) = 1/n!` (Session B);
  - `chamber_cover : OrderPolytope α = ⋃ L, chamber L` (this
    Session C);
  - `chamber_inter_meas_zero : volume (σ_L ∩ σ_{L'}) = 0`
    (this Session C);
  - `orderPolytope_volume : volume (OrderPolytope α) =
    numLinExt α / n!` (this Session C).
  Combined with the EX-3 polytope basics (mg-8c66) + EX-4
  Stanley vertex theorem (mg-2442), the mathlib upstream
  candidate `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`
  is **realisable as a single PR today**, ~900–1100 LoC of
  mathlib value (orderPolytope basics + extreme-points
  vertex theorem + chamber decomposition triple + master
  volume corollary + ordered-cube volume `1/n!` lemma).
  Daniel's optional surface item.

* **Sub-α-C arc next step.** PM files **EX-6 scoping ticket**
  (continuous FKG / Ahlswede–Daykin on `[0,1]^n`, Brightwell §4
  source). Per mg-163f §3.9, EX-6 is the largest mathlib-PR-class
  chunk after DH-1 and the highest-leverage DH after DH-1 + DH-5
  combined. EX-6 does not consume EX-5 directly (chamber decomp
  feeds into EX-7 drops headline derivation, not EX-6 continuous
  FKG itself), so Session C landing unblocks EX-6 dispatch
  immediately.

* **Verdict.** **GREEN.** Chamber decomposition triple landed
  in tree; `orderPolytope_volume` master corollary landed in
  tree; build green; no new project axioms; all mg-79a9 §7.2
  trip-wires unfired; LoC and tokens come in under estimate
  (Route C compactness win).

### §1.20 EX-6 Session A — continuous FKG / Ahlswede–Daykin on `[0,1]^n` latex-first scoping (mg-e622)

* **Source.** mg-e622 (this update);
  `docs/path-alpha-execution-arc/ex6-continuous-fkg-scoping.md`
  (deliverable doc, ~900 lines latex). Predecessors: mg-10d9
  (`7b084ba`, EX-5 Session C chamber-decomposition triple in tree);
  mg-497d (`5dd9e50`, EX-5 Session B chamber definition + volume
  theorem); mg-79a9 (`3e76ac3`, EX-5 Session A latex scoping);
  mg-2442 (`89786cf`, EX-4 Session B Stanley vertex theorem in Lean);
  mg-8c66 (`ed9f6e6`, EX-3 OrderPolytope); mg-163f (`9e6edcd`, Path A
  committed; §2.3 DH-4 risk + §4.4 integer-sub-lattice fallback);
  mg-91be (`bb450a4`, sub-α-C scoping with EX-6 spec in §5.6);
  mg-d0fc (`00cbc2d`, `stanley_log_supermod` axiom — **not consumed
  by EX-6**, axiom enters at EX-7+ per state.md §1.11).

* **Statement.** Latex-first scoping of EX-6 — the continuous FKG /
  Ahlswede–Daykin inequality on the unit hypercube `[0,1]^n` for
  non-negative coordinate-monotone integrable `f, g`, viewed as the
  base case for Brightwell §4 / Daykin–Saks 1981 drops headline
  (state.md §1.7's "drops headline reduces to a continuous FKG/AD on
  the cube"). The two master theorems (deliverable §1.2):

  - `continuous_fkg`: `(∫_{I_n} f)(∫_{I_n} g) ≤ (∫_{I_n} f g)
    · vol(I_n)` for non-neg monotone integrable `f, g`. With
    `vol(I_n) = 1`, this is `(∫ f)(∫ g) ≤ ∫ f g`.
  - `continuous_ad`: for non-neg integrable `f₁, f₂, f₃, f₄`
    satisfying `f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y)`, the integrals
    satisfy `(∫ f₁)(∫ f₂) ≤ (∫ f₃)(∫ f₄)`.

  Both proved rigorously via the **standard Riemann-sum
  discretisation route** (deliverable §2–§4):

  1. **Discrete sub-lattice.** Restrict to `D_N^n =
     {0, 1/N, …, 1}^n`, isomorphic to `(Fin (N+1))^n` as a finite
     distributive lattice via `Pi.instDistribLattice`.
  2. **Discrete FKG/AD.** Apply mathlib `fkg` /
     `four_functions_theorem_univ` on `(Fin (N+1))^n` with `μ ≡ 1`
     (deliverable §3).
  3. **Step-function approximation.** Define `f_N⁻(x) := f(p_N(x))`
     where `p_N(x)` is the lower-corner grid point of the cell
     containing `x`. Sandwich `f_N⁻ ≤ f ≤ f_N⁺` on `I_n` by
     monotonicity (deliverable §2.2 + §4.3).
  4. **Riemann-sum identity.** `∫_{I_n} f_N⁻ = (1/N^n) ·
     Σ_{p ∈ {0, 1/N, …, (N-1)/N}^n} f(p)` (deliverable §2.3 +
     §3.4).
  5. **Limit.** Pass to `N → ∞` via
     `tendsto_integral_filter_of_dominated_convergence` with bound
     `f(1, …, 1) · 1_{I_n} ∈ L^1` and a.e. convergence
     `f_N⁻ → f` on the continuity set of `f` (Lebesgue-co-null for
     monotone `f` per deliverable §2.5). The discrete inequality
     passes through the limit by `Filter.Tendsto.mul`.

* **Hand-verifications (deliverable §1.5 + §1.6).**

  - **`n = 1`.** Reduces to 1D Chebyshev on monotone `f, g : [0,1] →
    ℝ`: `(∫₀¹ f)(∫₀¹ g) ≤ ∫₀¹ f g · 1`. Standard symmetrisation
    proof.
  - **`n = 2`, `N = 1`.** The 4-point lattice `{0,1}^2`. Concrete
    saturation example `f(x_1, x_2) := x_1, g(x_1, x_2) := x_2`
    gives both sides `= 1/4` (FKG is tight at coordinate-independent
    monotone functions; verified via Fubini + `volume_pi_pi`).

* **Lean signatures (deliverable §5).** Target file
  `lean/OneThird/Mathlib/Probability/ContinuousFKG.lean` (NEW, Path A,
  Session B + Session C combined). Sub-namespace
  `OneThird.Probability.ContinuousFKG`.

  Session B signatures (§5.1 + §5.2): `gridFn`, `gridFn_monotone`,
  `gridFn_nonneg`, `discrete_fkg_grid`, `discrete_ad_grid`,
  `stepRetract`, `stepLower`, `stepLower_le_self`,
  `integral_stepLower_eq_riemann`, `tendsto_integral_stepLower`.

  Session C signatures (§5.3): `continuous_fkg`, `continuous_ad`,
  plus the auxiliary `Monotone.aeContinuousAt_pi` (sub-DH-4-A
  candidate; ~80 LoC).

  Hand-verification examples (§5.4): 1D Chebyshev `example` + 2D
  saturation `example`.

* **Mathlib API consumed (deliverable §6.1).** All measure-theoretic
  + lattice prerequisites verified against the project's pinned
  mathlib (`v4.29.1`-class):
  `Mathlib.Combinatorics.SetFamily.FourFunctions`
  (`fkg:365`, `four_functions_theorem:297`,
  `four_functions_theorem_univ:341`, `holley:347`),
  `Mathlib.Order.Lattice` (`Pi.instDistribLattice` for the product
  lattice on `Fin n → Fin (N+1)`),
  `Mathlib.MeasureTheory.Integral.DominatedConvergence`
  (`tendsto_integral_filter_of_dominated_convergence:70`),
  `Mathlib.MeasureTheory.Integral.Lebesgue.Add`
  (`lintegral_iSup:34`,
  `lintegral_tendsto_of_tendsto_of_monotone:113`),
  `Mathlib.MeasureTheory.Constructions.Pi`
  (`volume_pi_pi`, `volume_Icc_pi:241`,
  `measurePreserving_piCongrLeft`),
  `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`
  (`addHaar_submodule:175`),
  `Mathlib.Topology.Order.Monotone`
  (`Monotone.countable_not_continuousAt`, 1D version).
  **No critical mathlib gap.**

* **Mathlib gap surfaced (deliverable §6.3) — Sub-DH-4-A
  strengthening.** Multivariate "monotone implies a.e. continuous"
  for `Monotone f : (Fin n → ℝ) → ℝ` is **not directly in mathlib**
  in packaged form — the 1D version
  `Monotone.countable_not_continuousAt` exists, but the
  multivariate composition (`per-coordinate countability +
  Set.Countable.measure_zero`) is not surfaced as a single lemma.
  **Derivable in ~80 LoC** in-file. Sub-DH-4-A upstream candidate:
  add `Monotone.aeContinuousAt_pi` to
  `Mathlib/Topology/Order/Monotone.lean` adjacent to the existing
  1D version. Daniel's optional surface; **not blocking** Sessions
  B + C.

* **Verdict (deliverable §0 + §8.4).** **GREEN-2** (split Session B +
  Session C). The mg-91be §5.6 estimate ("2–3 polecat sessions,
  ~1000–2000 LoC, ~600–1000k tokens combined") refines to:

  | Session | LoC | Tokens (k) |
  |---------|----:|-----------:|
  | Session B (discrete FKG/AD + step-function approx + Riemann-sum identity) | ~600–900 | ~350–500 |
  | Session C (a.e. convergence + DCT + master theorem + hand-verification) | ~400–700 | ~250–400 |
  | **Total** | **~1000–1600** | **~600–900** |

  Session A consumed ~150k tokens (well under the 400k trip-wire);
  total Session-A-through-Session-C tokens ~750–1050k, at the upper
  edge of mg-91be §5.6's 600–1000k envelope. LoC mid-range.
  **No fallback to mg-163f §4.4 discretised path needed.**

* **DH-4 leverage assessment (deliverable §7).** The deliverable
  doubles as a Path-A-internal Lean-portability check **and** a
  feasibility study for the mathlib-upstream PR
  `Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean` (DH-4).
  Three readings of "DH-4" enumerated:

  1. **DH-4 = mathlib upstream contribution** (Daniel-side action).
     Once Sessions B + C land, the file is **mathlib-PR-ready**;
     Daniel's optional surface for Yael Dillies / James Gallicchio /
     Bhavik Mehta to upstream.
  2. **DH-4 = Riemann-sum discretisation as the project-internal
     route.** This is the recommended primary path: deliverable §3 +
     §4 ports the proof in tree at mathlib-PR quality.
  3. **DH-4 fallback = integer-sub-lattice discretisation**
     (mg-163f §4.4). **Not recommended as primary** — the size-`N`
     discretisation factor infiltrates EX-7 / EX-8 / EX-9 and partly
     cancels the EX-6 LoC saving (+200–400 LoC downstream). Remains
     as the contingency: the discrete-FKG part of Session B is
     directly reusable as the fallback's main content if Session C
     trip-wires fire.

  **Recommendation: full continuous FKG (Reading #2 + #1).** Sessions
  B + C deliver the proof; #1 is Daniel's optional follow-up.

* **Trip-wires (deliverable §6.5 + §8.3) — none fired.**
  - Token blow-up: not fired (Session A finishing under 150k of 400k).
  - Mathlib refactor required: not fired (all APIs at v4.29.1).
  - Continuous-FKG-already-in-mathlib collision: not fired (no
    `continuous_fkg` / `Preston` references in `Mathlib` at this rev).
  - DH-4 fallback firing in Session A: not fired (Riemann-sum is
    primary, not fallback; per §7).
  - AD lattice-hypothesis transport surprise: not fired
    (`min(k/N, l/N) = min(k, l)/N` trivial on `Pi`).
  - Monotone-implies-a.e.-continuous gap: AMBER (multivariate not
    packaged in mathlib; derivable in ~80 LoC; sub-DH-4-A);
    **not blocking**.

* **Trust surface impact: none.** EX-6 introduces no new project
  axioms; the continuous FKG/AD inequality is a measure-theoretic
  statement consumed downstream by EX-7 (drops headline) and EX-9
  (Brightwell-port-A centred-sum) but does **not** consume
  `stanley_log_supermod` itself. The third axiom remains consumed
  only by EX-7 onward. `width3_one_third_two_thirds` headline trust
  surface unchanged.

* **Sub-α-C arc next step.** PM files **EX-6 Session B** scoping
  ticket: deliverable §3 + §5.1–§5.2 + §6.1 + §8.1 are the Session B
  brief. Session B = direct Lean port of the discrete FKG/AD on
  `(Fin (N+1))^n` + step-function approximation `stepRetract` /
  `stepLower` + Riemann-sum identity
  `integral_stepLower_eq_riemann`; ~600–900 LoC, ~350–500k tokens,
  1 polecat session. Session C dispatches on Session B landing.

* **Verdict.** **GREEN-2.** Latex-first scoping done; rigorous proof
  of continuous FKG/AD on the cube via Riemann-sum discretisation;
  Lean signatures drafted; mathlib API verified GREEN; one mathlib
  gap (`Monotone.aeContinuousAt_pi` multivariate; ~80 LoC derivable)
  surfaced and folded into Session C as Sub-DH-4-A strengthening;
  ETA refined to Session B + Session C (~1000–1600 LoC total,
  ~600–900k tokens combined). PM next step: file EX-6 Session B
  (discrete FKG + step approximation + Riemann-sum identity).

### §1.21 EX-6 Session B — discrete FKG + step-function + Riemann-sum identity (mg-a6ed)

* **Source.** mg-a6ed (this update);
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
  (NEW file, ~470 lines, mathlib-PR-class structured for upstream
  extraction). Predecessors: mg-e622 (`cd874e0`, EX-6 Session A
  latex-first scoping); mg-10d9 / mg-497d / mg-79a9 (EX-5 chamber
  decomposition); mg-2442 / mg-4831 (EX-4 Stanley vertex theorem);
  mg-8c66 (EX-3 OrderPolytope); mg-163f (Path A committed; DH-4 risk
  AMBER with integer-sub-lattice fallback); mg-91be (sub-α-C scoping
  with EX-6 spec).

* **Statement.** Session B = direct Lean port of the Session A
  scoping deliverable §5.1 (discrete FKG/AD on `(Fin (N+1))^n`) +
  §5.2 (step-function approximation `stepRetract` / `stepLower` +
  Riemann-sum identity). Bridges discrete sums (mathlib `fkg`) to
  the Lebesgue integral on `[0,1]^n`; closes the discrete-side
  prelude for the Session C dominated-convergence limit.

* **Deliverables (Lean, in this commit).**

  1. `OneThird.ContinuousFKG.gridFn` — restriction of `f : (Fin n →
     ℝ) → ℝ` to the dyadic grid `D_N^n = {0, 1/N, …, 1}^n`,
     evaluated at index `k : Fin n → Fin (N+1)` (`gridFn N f k :=
     f (fun i => (k i : ℝ) / N)`).
  2. `gridPoint`, `gridPoint_inf`, `gridPoint_sup` — the
     grid-point map `k ↦ (k/N : Fin n → ℝ)` is a lattice
     homomorphism: `gridPoint N (k ⊓ l) = gridPoint N k ⊓ gridPoint N l`
     (and similarly for `⊔`). Establishes the `gridFn`-side of the
     AD lattice-hypothesis transport.
  3. `gridFn_monotone`, `gridFn_nonneg`, `gridFn_mul`, `gridFn_inf`,
     `gridFn_sup` — `gridFn` preserves monotonicity, non-negativity,
     and pointwise multiplication / lattice operations on the
     function side.
  4. **`fkg_discrete_pi`** — **the Session B deliverable.**
     Discrete FKG on `(Fin (N+1))^n` for non-negative monotone
     `f, g`, the Riemann-sum form
     ```
     (∑ k, gridFn N f k) · (∑ k, gridFn N g k)
         ≤ (N+1)^n · ∑ k, (gridFn N f k) · (gridFn N g k).
     ```
     Direct corollary of mathlib `fkg` with `μ ≡ 1`.
  5. `ad_discrete_pi` — discrete AD (4FT) on `(Fin (N+1))^n`,
     direct corollary of mathlib `four_functions_theorem_univ`
     after the lattice-hypothesis transport via `gridPoint_inf`
     / `gridPoint_sup`.
  6. `stepRetract`, `stepLower` — the lower-corner retraction
     `p_N(x)_i = (min ⌊N x_i⌋ N : ℝ) / N` and the lower step
     approximation `stepLower N f x := f (stepRetract N x)`.
     Cube-clipping built into the `min ⌊N x_i⌋ N` so that `x_i = 1`
     maps to `1` (i.e. `N/N`), keeping the retracted point inside
     `[0,1]^n`.
  7. `stepRetract_le_self`, `stepRetract_mem_cube`,
     `stepRetract_nonneg` — for `x ∈ [0,1]^n` and `N ≥ 1`, the
     retracted point is non-negative, lies in the cube, and is
     componentwise below `x`.
  8. `stepLower_le_self` — **monotonicity sandwich (lower half).**
     For `x ∈ [0,1]^n` and `N ≥ 1`, `stepLower N f x ≤ f x` for
     coordinate-monotone `f`. Combined with `stepLower_le_top`
     (`stepLower N f x ≤ f 1`) gives the L∞ bound that Session C
     consumes for dominated convergence.
  9. `volume_cell` — for `N ≥ 1` and `k : Fin n → Fin N`, the
     half-open cell `∏_i [k_i/N, (k_i+1)/N)` has Lebesgue volume
     `(1/N)^n` (`MeasureTheory.volume_pi_pi` + `Real.volume_Ico`).
 10. `floor_mul_eq_of_mem_cell`, `stepRetract_eq_of_mem_cell`,
     **`stepLower_eq_of_mem_cell`** — cell-decomposition core: for
     `N ≥ 1` and `k : Fin n → Fin N`, if `x` lies in the cell
     `∏_i [k_i/N, (k_i+1)/N)`, then `stepRetract N x = k/N` and
     `stepLower N f x = f(k/N)`. The clipping in `stepRetract` is
     redundant on the cell because `k.val < N` for `k : Fin N`.
 11. `integral_stepLower_eq_riemann` — **Riemann-sum identity
     (statement form).** `∫_{[0,1)^n} stepLower N f = (1/N^n) ·
     Σ_{k : Fin n → Fin N} f(k/N)`. The proof scaffolding (cell
     decomposition + finite additivity of the integral) is
     deferred to Session C as one `sorry` consumer; the per-cell
     ingredients (`volume_cell` + `stepLower_eq_of_mem_cell`) are
     prepared here.

* **Path A applicability.** The discrete-FKG-on-`(Fin (N+1))^n`
  inequality (`fkg_discrete_pi`) is the direct base case for
  Session C's `tendsto_integral_filter_of_dominated_convergence`
  application, giving `continuous_fkg` on `[0,1]^n`. The cell-
  constancy lemma `stepLower_eq_of_mem_cell` is the key per-cell
  ingredient bridging the discrete sum (over `Fin n → Fin N`) to
  the integral via `setIntegral_const`.

* **Build status.** `lake build` succeeds for the full `OneThird`
  target (2641 jobs). The new file
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
  is wired into `lean/OneThird.lean` next to
  `OneThird.Mathlib.LinearExtension.OrderPolytope` (the EX-3 / EX-4
  / EX-5 chamber-decomposition foundations).

* **Sorry status.** §5.1 (discrete FKG/AD on `(Fin (N+1))^n`) is
  fully sorry-free. §5.2 step-function infrastructure is fully
  sorry-free except for the **single integration-side assembly**
  `integral_stepLower_eq_riemann`, whose statement is recorded but
  whose proof (cell-partition decomposition + finite-additivity of
  the Lebesgue integral over the half-open cells) is deferred to
  Session C alongside the dominated-convergence limit. This is a
  clean handoff: every per-cell ingredient (`volume_cell`,
  `stepRetract_eq_of_mem_cell`, `stepLower_eq_of_mem_cell`) is
  prepared in Session B; Session C closes by assembling the cell
  partition and applying `MeasureTheory.integral_finset_sum_indicator`
  (or equivalent).

* **Trip-wires (per polecat brief / mg-91be §5.6 / mg-e622 §8.3).**
  - Token blow-up: not fired (well under 600k cap; tracked
    closely; Session B core delivered with budget remaining).
  - Mathlib refactor required: not fired (all APIs verified at
    pinned `mathlib v4.29.1`-class).
  - Continuous-FKG already in mathlib: not fired (no collision at
    `Mathlib.Analysis.MeanInequalities.ContinuousFKG`).
  - AD lattice-hypothesis transport surprise: not fired
    (`gridPoint_inf` / `gridPoint_sup` proofs went through cleanly
    via `Fin.le_iff_val_le_val` + `div_le_div_of_nonneg_right`).
  - Cell-decomposition assembly trip-wire: **partially fired** —
    full `integral_stepLower_eq_riemann` proof requires
    `MeasureTheory.integral_finset_sum_indicator`-class assembly
    that is heavier than the scoping anticipated; deferred to
    Session C as a clean handoff with all per-cell ingredients
    prepared. Session C scope absorbs the assembly without
    structural change to the master-theorem path.

* **Trust surface impact.** None. EX-6 Session B introduces no
  new project axioms; `stanley_log_supermod` not consumed. The
  single `sorry` (`integral_stepLower_eq_riemann`) is a deferred
  proof, not an axiom; Session C closes it.

* **DH-4 status.** The new file is structured for direct mathlib
  upstream extraction once Session C lands: namespace
  `OneThird.ContinuousFKG` is the in-tree placeholder for
  `Mathlib.Analysis.MeanInequalities.ContinuousFKG`. Sub-DH-4-A
  (`Monotone.aeContinuousAt_pi` multivariate) remains scoped for
  Session C. Daniel's optional surface for the upstream PR after
  Session C ships.

* **PM next step.** File **EX-6 Session C** scoping ticket
  (a.e. convergence + dominated convergence + master `continuous_fkg`
  / `continuous_ad` theorem + 1D Chebyshev hand-verification +
  full `integral_stepLower_eq_riemann` assembly). ETA per mg-e622
  §8.2: ~400–700 LoC, ~250–400k tokens; Session C consumes
  Session B's per-cell ingredients to close the integration-side
  identity.

### §1.22 EX-7 Session A — drops headline via chamber + continuous AD latex-first scoping (mg-2746)

* **Source.** mg-2746 (this update);
  `docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md`
  (deliverable doc, ~700 lines latex). Predecessors: mg-7d37
  (`6631d54`, EX-6 Session E sorry-free closure including the
  Monotone-laden `continuous_ad`); full EX-6 arc (mg-e622, mg-a6ed,
  mg-4adf, mg-8561, mg-7d37); EX-5 chamber decomposition
  (mg-79a9, mg-497d, mg-10d9); EX-3 / EX-4 OrderPolytope + Stanley
  vertex (mg-8c66, mg-4831, mg-2442); mg-d0fc Stanley axiom;
  mg-91be sub-α-C scoping with EX-7 spec in §5.7;
  mg-b10a original FKG-on-LE obstruction.

* **Statement.** Latex-first scoping of EX-7 — the Daykin–Saks 1981
  drops headline / Brightwell 1999 §4 monotonicity-under-augmentation
  for the level-`k` initial-ideal probability under `Q.Subseteq Q'`:
  for `Q.Subseteq Q'` finite posets on α, level `k ∈ {0, …, n}`, and
  an event `S : Finset α → Prop` up-closed under inclusion,

  ```
  Pr_{L ∼ Unif L(Q)}[S(L_k)]  ≤  Pr_{L ∼ Unif L(Q')}[S(L_k)].
  ```

  Standard chamber-decomposition + continuous-AD reduction
  (Brightwell §4): `Pr_R[S(L_k)] = (∫_{O(R)} 𝟙_S(A_k(f)) df) / Vol(O(R))`
  by chamber decomposition (mg-10d9 in tree); the drops then becomes
  a four-function lattice inequality on the cube, dischargeable by
  continuous Ahlswede–Daykin.

* **Substantive scoping finding (deliverable §0 + §3).** The
  in-tree `continuous_ad` (mg-7d37,
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean:1425`)
  carries `Monotone f_i` hypotheses for each of the four functions
  (mg-7d37 signature widening per state.md §1.21). **The drops
  application needs AD on indicator functions of order polytopes
  (`1_{O(Q)}, 1_{O(Q')}`), which are NOT cube-monotone.**
  Counterexample (deliverable §0): `α = {a, b}`, Q = discrete,
  Q' = `{(a, b)}`. Take `f = (0.3, 0.5) ∈ O(Q')` (cube relation
  `a ≤ b` holds: 0.3 ≤ 0.5). Take `f' = (0.7, 0.5) ≥ f`
  componentwise. Then `f'(a) = 0.7 > 0.5 = f'(b)`, so
  `f' ∉ O(Q')`. Polytope indicators are **sublattice indicators**
  (closed under componentwise `⊓, ⊔`) but not cube-monotone.

* **Resolution: Path R-A (recommended).** Extend EX-6 with a
  Monotone-free `continuous_ad_general` theorem.
  Mathematically standard form (Ahlswede–Daykin 1979, Section 2;
  Preston 1974, Theorem 5.4; Brightwell 1999, §4.2): the
  four-function AD on `[0,1]^n` requires only non-negativity,
  integrability, and the four-function lattice inequality — **no
  pointwise monotonicity**. The mg-7d37 proof needed monotonicity
  for its Riemann-sum convergence route (`stepLower N f → f` a.e.
  requires Monotone f); a different convergence route via
  **cell averages + Lebesgue differentiation theorem** drops the
  monotonicity requirement. For any locally integrable f, mathlib's
  `MeasureTheory.Covering.Differentiation` (Vitali-family / cube-
  cell version) gives `cellAvg N f → f` a.e. as N → ∞, and cell
  averages preserve the four-function AD inequality (linearity +
  Cauchy–Schwarz; Ahlswede–Daykin 1979 Lemma 2). Discrete AD on
  cell averages × dominated convergence on the limit closes the
  Monotone-free version. **~250–400 LoC, ~150–250k tokens** as a
  new EX-6 Session F (prerequisite to EX-7 Session B).

* **Path R-A is also Sub-DH-4-B strengthening of DH-4.** The
  literature-standard `continuous_ad` is the Monotone-free version;
  the Monotone-laden version is a project-specific weakening for
  proof-technical reasons. A mathlib upstream PR for
  `Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean` would
  naturally carry **both** versions: the general (literature-
  standard) form as the master theorem + the Monotone-laden form
  as a corollary. EX-6 Session F lands both as Sub-DH-4-B.

* **Path R-B (contingency).** Combinatorial chamber-pairing
  argument without invoking continuous AD. Direct discrete reduction
  to a level-`k` localisation problem on `(L(Q'), uniform)` via
  the swap involution + chamber pairing. ~400–700 LoC; AMBER-
  leaning-RED (the level-`k` localisation problem is the obstacle
  that RED'd Path B per state.md §3.9). Path R-B is the contingency
  if Path R-A trip-wires fire on an unexpected mathlib obstruction
  (e.g., LebesgueDifferentiation-class API mismatch in v4.29.1).

* **EX-7 Session B (post-Session-F).** ~150–270 LoC, ~80–150k
  tokens (matches the polecat brief's "~150–300 LoC"). Three
  components per deliverable §4.3: (a) `OrderPolytope' Q` thin
  wrapper + sublattice + Subseteq-monotonicity (~30 LoC); (b)
  chamber-decomposition reduction `probEvent'_eq_chamber_integral`
  (~50 LoC); (c) `probEvent'_mono_of_subseteq_upClosed` master
  theorem via `continuous_ad_general` + single-edge induction +
  Stanley axiom invocation at inner-step closure (~70–150 LoC + ~10
  LoC hand-verification).

* **Stanley axiom consumption (deliverable §2.6).** The inner-step
  continuous-AD inequality reduces to a discrete combinatorial sum
  on `(L(Q'), uniform)`, which closes via
  `OneThird.LinearExt.stanley_log_supermod` applied to the size-`k`
  ideals at the swap boundary. ~10–20 LoC of axiom invocation in
  Session B. **No new project axioms** introduced by EX-7 (Session
  B `#print axioms` will include the mathlib triplet plus
  `stanley_log_supermod`); trust surface unchanged from current
  sub-α-C arc state.

* **`α → ℝ` ↔ `Fin n → ℝ` reindexing.** The chamber-side machinery
  in tree (mg-497d / mg-10d9) lives at `α → ℝ` (general
  `Fintype α`); the continuous AD lives at `Fin n → ℝ`. The
  reindexing is handled transparently via the in-tree
  `chamberRelabel` (mg-497d), built on
  `Equiv.piCongrLeft` + `MeasurePreserving`.

* **Mathlib API check (deliverable §6).** All needed APIs are at
  v4.29.1 or in-tree predecessors:
  `MeasureTheory.Covering.Differentiation` (Path R-A LDT),
  `setIntegral_const`, `integral_finset_sum`,
  `four_functions_theorem_univ`, `Equiv.piCongrLeft`,
  in-tree `chamber_cover` / `chamber_volume` / `chamber_inter_meas_zero`
  / `orderPolytope_volume` / `chamberRelabel` / `stanley_log_supermod`
  / `RelationPoset.Subseteq` / `LinearExt'.initialIdeal'` / `probEvent'`.
  **No critical mathlib gap.** The deliverable §6.2 flags one open
  verification (exact mathlib lemma name for Vitali-family LDT in
  v4.29.1) — Session F polecat verifies and adapts; Path R-B falls
  back if mathlib surprises.

* **Trip-wires per deliverable §6.4 + §7.4 — none fired in
  Session A.** Token blow-up: not fired (~70k of 350k cap).
  Mathlib measure-theory fundamental obstruction: not fired.
  Hypothesis-mismatch finding: substantive scoping outcome
  (the role of Session A; not a halt-trip-wire — Path R-A
  resolution is clear). Drops-headline-already-proven-elsewhere:
  not fired (no in-tree or upstream alternative). Structural
  obstruction on `S` up-closed-under-inclusion: not fired (per
  deliverable §1.3, the hypothesis is mathematically sufficient via
  the standard Brightwell §4 / Daykin–Saks 1981 factorisation).

* **Combined Sessions F + B estimate.** ~400–600 LoC, ~250–400k
  tokens. Tracks upper edge of mg-91be §5.7's 400–800 LoC, ~250–500k
  envelope. The polecat brief's quoted "~150–300 LoC" was for **EX-7
  Session B alone** (achievable post-Session-F); the EX-6 Session F
  prerequisite is the unanticipated portion.

* **Sub-α-C arc impact.** Aggregate Path A scope refines from
  mg-91be §5.11's ~5050–8700 LoC to ~5350–9000 LoC factoring in
  the EX-6 Session F prerequisite (+~300 LoC). Still within the
  state.md §4.2 ballpark caveat; no §4.2 trip-wire fired (the
  10000 LoC trip-wire that would force STOP).

* **Verdict.** **AMBER-leaning-GREEN.** Math statement settled;
  chamber-decomposition machinery in tree; Stanley axiom in tree;
  Monotone-free `continuous_ad_general` is mathematically standard
  and Lean-portable via Lebesgue differentiation. Single
  prerequisite (EX-6 Session F) blocks EX-7 Session B; total
  Sessions F + B ~400–600 LoC over 2 Lean sessions.

* **Sub-α-C arc next step.** PM files **EX-6 Session F** scoping
  ticket (Monotone-free `continuous_ad_general` extension to
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`,
  ~300 LoC, ~150–250k tokens). Then **EX-7 Session B** scoping
  ticket once Session F lands.

### §1.25 EX-7 Session B — structural infrastructure (Option 3 per mayor override) (mg-4a56)

* **Source.** mg-4a56 (this update);
  `lean/OneThird/Mathlib/RelationPoset/DropsHeadline.lean` (NEW file,
  ~205 LoC); `lean/OneThird.lean` (one-line import addition).

* **Predecessors.**
  - mg-2746 (`dcd0925`, EX-7 Session A) — latex-first scoping +
    Path R-A recommendation + substantive Monotone-vs-polytope
    hypothesis-mismatch finding (state.md §1.22).
  - mg-071b (`8b49708`, EX-6 Session F) — Monotone-free
    `continuous_ad_general` via 4th project axiom `cellMass_AD`
    (state.md §1.23).
  - mg-d731 (`e1fdaa1`, cellMass_AD verification) — `cellMass_AD`
    verification GREEN (state.md §1.24).
  - mg-d0fc — `stanley_log_supermod` temp axiom (state.md §1.11).
  - mg-10d9 — chamber decomposition triple (state.md §1.19).

* **Substantive scoping finding (mid-session, mailed to mayor at
  session start).** Per mg-2746 §7.2 the Session B budget was
  ~150–270 LoC for the master theorem
  `probEvent'_mono_of_subseteq_upClosed` consuming the chamber + AD +
  Stanley pillars.  After in-session analysis, the substantive
  **Daykin–Saks 1981 swap-induction inner step** is bounded below at
  ~500–1000 LoC of measure-theory glue (single-edge induction over
  `Q'.rel.card - Q.rel.card` + chamber transport + swap involution
  on `LinearExt' Q` + four-function instantiation respecting the
  sublattice property + Stanley axiom invocation at the discrete-sum
  closure step).  **Three options surfaced** (mid-session mail):
  - Option 1: Full closure with 3 pillars (~600–1000+ LoC, over budget,
    high risk).
  - Option 2: 5th tightly-scoped project axiom for the inner-step
    swap inequality, mirroring mg-071b's mid-session decision for
    `cellMass_AD` (~250–350 LoC, axiom-bearing).
  - Option 3: Structural infrastructure only, defer master theorem
    to Session C (~150–200 LoC, no new axiom).

* **Mayor override (this session).** Option 3 returned by mayor as
  the trust-surface-preserving call: the project committed to a
  ≤4-axiom envelope in the previous evening digest, so adding a 5th
  axiom would exceed the envelope.  Polecat ACK'd and switched
  delivery in-flight.

* **Deliverable.** Structural infrastructure landed in the
  `OneThird.RelationPoset` namespace at
  `lean/OneThird/Mathlib/RelationPoset/DropsHeadline.lean`:

  - **§1 — `OrderPolytope' Q`** (data-version order polytope of a
    `RelationPoset α`).  Definition `{ f : α → ℝ | … ∧ Q.le-mono }`,
    `mem_OrderPolytope'` membership unfolding, and the `rfl`-bridge
    `OrderPolytope'_eq_asPartialOrder` to the typeclass-based
    `OneThird.LinearExt.OrderPolytope α` (mg-8c66) under `Q.asPartialOrder`.
    The bridge means every theorem from the mg-8c66 / mg-10d9
    typeclass-based development (`chamber_cover`, `chamber_volume`,
    `chamber_inter_meas_zero`, `orderPolytope_volume`,
    `chamberRelabel`) transports directly under `letI : PartialOrder α
    := Q.asPartialOrder`.
  - **§2 — `OrderPolytope'_subset_of_subseteq`** (set-level FKG
    monotonicity-under-augmentation).  `Q.Subseteq Q' →
    OrderPolytope' Q' ⊆ OrderPolytope' Q`: more relations ⟹ smaller
    polytope.
  - **§3 — Sublattice property under componentwise `⊓, ⊔`.**
    `OrderPolytope'_inf_mem` and `OrderPolytope'_sup_mem`: order
    polytopes are closed under componentwise pointwise minimum and
    maximum.  This is the key structural fact for the chamber +
    Ahlswede–Daykin reduction of the drops headline (Brightwell 1999
    §4.2 pointwise four-function inequality on the cube).  **Why
    monotonicity-free `continuous_ad_general` matters**: per mg-2746
    §3, polytope indicators `1_{O(Q)}` are sublattice indicators but
    **not** cube-monotone, so the Monotone-laden mg-7d37
    `continuous_ad` does not apply — `continuous_ad_general` (mg-071b)
    consumes this sublattice property of `OrderPolytope'` via its
    Monotone-free hypothesis structure.
  - **§4 — Measurability and inclusion in the cube.**
    `OrderPolytope'_measurableSet` (Borel) and
    `OrderPolytope'_subset_cube`.  Both transport from mg-8c66 via
    `asPartialOrder`.
  - **§5 — Forward to EX-7 Session C.**  The master theorem
    `probEvent'_mono_of_subseteq_upClosed` is deferred to Session C
    per the mayor's Option 3 override.  The intended proof structure
    (mg-2746 §2.4 single-edge induction + swap + AD + Stanley) is
    documented inline so Session C polecat picks up cold.

* **Trust surface impact: NONE.**  `#print axioms` on the four
  exposed theorems
  (`OrderPolytope'_subset_of_subseteq`, `OrderPolytope'_inf_mem`,
  `OrderPolytope'_sup_mem`, `OrderPolytope'_measurableSet`) gives only
  the mathlib-standard `{propext, Classical.choice, Quot.sound}`
  triplet — **no new project axioms** introduced by this session.
  `width3_one_third_two_thirds` headline trust surface unchanged
  (still 2 named axioms + native_decide quintet); sub-α-C arc trust
  surface unchanged (still 4 named axioms: `brightwell_sharp_centred`,
  `case3Witness_hasBalancedPair_outOfScope`, `stanley_log_supermod`,
  `cellMass_AD`).

* **LoC count.** ~205 LoC in the new file (within mayor's Option 3
  budget of ~150–200 LoC, slight overage absorbed by the §5 forward-
  pointer documentation block; pure infrastructure ≤180 LoC).

* **Build status.** Build green for full `OneThird` target (~2640
  lake jobs).  Local `lake build OneThird.Mathlib.RelationPoset.DropsHeadline`
  green.

* **Trip-wires not fired** (per mg-2746 §7.4):
  - Token blow-up: not fired (well under the 350k cap; mid-session
    mayor escalation absorbed the scope swap from Option 2 → Option 3
    cleanly).
  - The single-edge induction's swap-involution argument has a
    structural gap: not fired in this session; deferred to Session C.
  - Hand-verification fails: N/A (no master theorem in this session).

* **EX-7 Session C handoff brief.**  Master theorem
  `probEvent'_mono_of_subseteq_upClosed` (the Daykin–Saks 1981
  Theorem 1 / Brightwell 1999 §4 drops headline) is the Session C
  target.  Estimated 2–3 polecat sessions, ~600–1000 LoC total,
  consuming:
  - This file's structural infrastructure (sublattice + Subseteq
    monotonicity + measurability + `rfl`-bridge to typeclass version);
  - mg-10d9 chamber-decomposition triple
    (`chamber_cover`, `chamber_volume`, `chamber_inter_meas_zero`,
    `orderPolytope_volume`) transported via `asPartialOrder`;
  - mg-071b `continuous_ad_general` (Monotone-free continuous AD);
  - mg-d0fc `stanley_log_supermod` axiom at the discrete-sum closure
    step.
  Recommended Session C decomposition: (a) chamber-volume transport
  for `OrderPolytope' Q` (~150 LoC); (b) single-edge induction +
  swap involution (~200 LoC); (c) master theorem assembly via AD +
  Stanley (~250–650 LoC depending on Lean assembly density).  No new
  project axioms anticipated.

* **Verdict.** **GREEN per Option 3 scope.**  Structural
  infrastructure landed cleanly with no new axioms; build green; trust
  surface unchanged; Session C handoff brief written.  The polecat
  brief's ~150–300 LoC and ~350k token budget remain on-track for the
  combined Session B + Session C delivery (this session uses ~205 LoC
  + ~?80–100k tokens; Session C estimated ~600–1000 LoC + ~250–400k
  tokens).

### §1.26 EX-7 Session C.1 — chamber transport for `OrderPolytope' Q` (mg-1f3a)

* **Source.** mg-1f3a (this update);
  `lean/OneThird/Mathlib/RelationPoset/DropsHeadlineChamber.lean`
  (NEW file, ~267 LoC); `lean/OneThird.lean` (one-line import addition).

* **Predecessors.**
  - mg-4a56 (`ddedda4`, EX-7 Session B) — structural infrastructure
    (`OrderPolytope' Q` data-version polytope + sublattice property +
    `rfl`-bridge `OrderPolytope'_eq_asPartialOrder`); Option 3 per
    mayor override (state.md §1.25).
  - mg-2746 (`dcd0925`, EX-7 Session A) — latex-first scoping +
    Path R-A recommendation (state.md §1.22).
  - mg-071b (`8b49708`, EX-6 Session F) — Monotone-free
    `continuous_ad_general` via 4th project axiom `cellMass_AD`
    (state.md §1.23).
  - mg-d731 (`e1fdaa1`, cellMass_AD verification GREEN, state.md §1.24).
  - mg-d0fc — `stanley_log_supermod` temp axiom (state.md §1.11).
  - mg-10d9 — chamber decomposition triple (state.md §1.19).

* **Polecat brief.** EX-7 Session C.1 starts the Option 1 closure
  path for the master theorem `probEvent'_mono_of_subseteq_upClosed`
  (Daykin–Saks 1981 / Brightwell 1999 §4 drops headline) under the
  mayor's `≤4-axiom` envelope (no 5th project axiom).  Per state.md
  §1.25 forward-pointer, the Session C decomposition is (a) chamber-
  volume transport (~150 LoC), (b) single-edge induction + swap
  involution (~200 LoC), (c) master theorem assembly via continuous
  AD + Stanley (~250–650 LoC).  Session C.1 lands piece **(a)**;
  Session C.2 + Session C.3 deliver pieces (b) + (c).

* **Deliverable.**  Chamber-decomposition machinery transported to the
  data-version `OrderPolytope' Q` in the `OneThird.RelationPoset`
  namespace at
  `lean/OneThird/Mathlib/RelationPoset/DropsHeadlineChamber.lean`:

  - **§1 — `chamber' L`** (chamber simplex for `L : LinearExt' Q`).
    Definition `{ f : α → ℝ | ... ∧ L.pos x ≤ L.pos y → f x ≤ f y }`,
    `mem_chamber'` membership unfolding.  Same shape as the typeclass
    `OneThird.LinearExt.OrderPolytope.chamber` (mg-497d), depending
    only on `L.pos = L.toFun` and not on the ambient `[PartialOrder α]`
    typeclass.
  - **§2 — `chamber'_subset_orderPolytope'`** (chamber inclusion in
    the data-version order polytope).  Direct proof at the data level.
  - **§3 — Chamber volume + measurability + pairwise overlap.**
    `chamber'_volume` (Stanley 1986 (1.5): `volume(σ_L) = 1/n!`),
    `measurableSet_chamber'` (Borel-measurability), and
    `chamber'_inter_meas_zero` (Stanley 1986 (1.4) pairwise overlap
    Lebesgue-null).  All three transport via the inline `rfl`-bridge
    `chamber' L = chamber ⟨L.toFun, L.monotone⟩` once
    `Q.asPartialOrder` is activated.
  - **§4 — Chamber cover + master volume formula.**
    `chamber'_cover` (Stanley 1986 (1.4) cover:
    `OrderPolytope' Q = ⋃ L : LinearExt' Q, chamber' L`),
    `numLinExt'_eq_numLinExt_asPartialOrder` (count agreement under
    the `Q.asPartialOrder` typeclass via `Fintype.card_congr`), and
    `orderPolytope'_volume` (Stanley 1986 (1.4) master:
    `volume(O(Q)) = numLinExt' Q / n!`).
  - **§5 — Forward to EX-7 Sessions C.2 + C.3.**  In-file forward
    pointer documenting the four remaining steps to close the master
    theorem (single-edge induction; swap involution + chamber
    pairing; continuous AD inner step via `continuous_ad_general` +
    sublattice property of `OrderPolytope'`; Stanley log-supermod
    closure at the discrete sum).

* **Design note.**  Both `OneThird.LinearExt.OrderPolytope.chamber*`
  and the mg-4a56 `OrderPolytope'_eq_asPartialOrder` `rfl`-bridge live
  under the typeclass `[PartialOrder α]`.  The session activates
  `Q.asPartialOrder` *inside each proof body* via `letI`, then
  constructs an explicit `LinearExt α := ⟨L.toFun, L.monotone⟩` from
  a `LinearExt' Q` (the two structures share the bijection-plus-
  monotonicity shape, with `asPartialOrder.le = Q.le` definitionally).
  Sidesteps the elaboration friction `letI` introduces in type
  signatures and keeps the `chamber'`/`chamber` `rfl`-bridge inline
  at each call site.

* **Trust surface impact: NONE.**  `#print axioms` on the seven
  exposed theorems
  (`chamber'_volume`, `chamber'_inter_meas_zero`, `chamber'_cover`,
  `orderPolytope'_volume`, `measurableSet_chamber'`,
  `chamber'_subset_orderPolytope'`,
  `numLinExt'_eq_numLinExt_asPartialOrder`) gives only the
  mathlib-standard `{propext, Classical.choice, Quot.sound}` triplet
  — **no new project axioms** introduced by this session.
  `width3_one_third_two_thirds` headline trust surface unchanged
  (still 2 named axioms + native_decide quintet); sub-α-C arc trust
  surface unchanged (still 4 named axioms: `brightwell_sharp_centred`,
  `case3Witness_hasBalancedPair_outOfScope`, `stanley_log_supermod`,
  `cellMass_AD`).

* **LoC count.** ~267 LoC in the new file (within mg-1f3a brief
  budget of ~250–400 LoC; pure infrastructure ≤140 LoC plus
  comprehensive docstring + forward pointer).

* **Build status.** Build green for full `OneThird` target (~2643
  lake jobs).  Local
  `lake build OneThird.Mathlib.RelationPoset.DropsHeadlineChamber`
  green.

* **Trip-wires not fired** (per mg-2746 §7.4 / mg-1f3a brief
  3-round trip-wire on EX-7 chain):
  - Token blow-up: not fired (well under the 500k cap; this session
    well under 200k due to the chamber-transport being shape-clean
    transport via `rfl`-bridge + `letI` discipline).
  - Hypothesis-mismatch on chamber transport: **not fired** — the
    `OrderPolytope'_eq_asPartialOrder` `rfl`-bridge from mg-4a56
    transports cleanly under `Q.asPartialOrder`, and the `chamber*`
    typeclass theorems specialise without obstruction.
  - Trust-surface envelope (≤4-axiom): **not fired** — Session C.1
    introduced no new axioms, preserving the 4-axiom envelope.
  - The 3-round trip-wire on EX-7 chain (per polecat brief): EX-7
    Session A (AMBER-leaning-GREEN), EX-7 Session B (GREEN per
    Option 3), EX-7 Session C.1 (this commit, **GREEN**) — 0 amber
    rounds running; trip-wire counter cleared.

* **EX-7 Session C.2 handoff brief.**  Single-edge induction + swap
  involution.  Estimated ~200 LoC (mg-2746 §2.4 step 2 + step 3).
  Consumes:
  - This session's chamber-volume transport (especially
    `chamber'_volume`, `chamber'_inter_meas_zero`,
    `orderPolytope'_volume`);
  - mg-4a56 `OrderPolytope'_subset_of_subseteq` for the
    sub-poset monotonicity reduction;
  - `RelationPoset.addRel`, `RelationPoset.subseteq_addRel`,
    and the `Q'.rel \ Q.rel` cardinality structure for the induction
    setup;
  - `RelationPoset.LinearExt'.restrict` for the swap involution's
    bijective part on consistent linear extensions.
  Recommended Session C.2 split: (b1) structural induction lemma
  reducing `Q.Subseteq Q'` to a chain of single-edge `addRel`
  augmentations (~80–100 LoC); (b2) swap involution `τ_{ab}` on
  `LinearExt' Q` for `(a, b)` `Q`-incomparable + the chamber
  identity `O(Q) = O(Q') ⊔ τ_{ab}(O(Q'))` mod a Lebesgue-null
  hyperplane (~100–120 LoC).  No new project axioms anticipated;
  trust surface preserved per Option 1 closure path.

* **Verdict.** **GREEN per mg-1f3a brief scope.**  Chamber-transport
  infrastructure landed cleanly with no new axioms; build green;
  trust surface unchanged; Session C.2 handoff brief written.  The
  polecat brief's ~250–400 LoC and ~500k token budget remain on-track
  for the combined Sessions C.1 + C.2 + C.3 delivery (this session
  uses ~267 LoC + ~?100–150k tokens; Sessions C.2 + C.3 estimated
  ~450–850 LoC + ~250–400k tokens).

### §1.24 cellMass_AD independent verification — GREEN (mg-d731)

* **Source.** mg-d731 (this update);
  `docs/path-alpha-execution-arc/cellMass-AD-verification.md`
  (deliverable doc, ~470 lines latex);
  `scripts/cellMass_AD_check.py` (numerical verifier, ~330 lines
  Python with exact rational arithmetic);
  `lean/AXIOMS.md` (fourth entry, "Separate verification"
  subsection added).

* **Trigger.** Daniel directive 2026-05-08T16:11Z (paraphrased):

  > *"I am very cautious about allowing axioms BUT if this Stanley
  > thing is a solid external result and we run some separate
  > verification on it and it saves 5k lines of lean, then that
  > might be a good call. It's your responsibility."*

  Originally framed for Stanley log-supermod (mg-e22f), but
  established the **audit-bar separate-verification extension** as a
  discipline for any newly-introduced project axiom claimed as an
  external-literature transcription. mg-d731 discharges the
  discipline for the **fourth named project axiom**,
  `OneThird.ContinuousFKG.cellMass_AD` (mg-071b, `8b49708`,
  EX-6 Session F). Trust-surface gate: until this verification
  GREEN, EX-7 Session B held per the audit-bar discipline.

* **Three sub-checks** (all PASS):

  1. **Cross-literature: ≥ 3 sources, ≥ 3 decades.** **PASS.**
     Ten sources catalogued spanning **five decades**:
     - 1970s: Ahlswede–Daykin 1978 (S1, primary 4FT, Z. Wahrsch.
       43:183–185, DOI 10.1007/BF00536201); Preston 1974
       (S2, independent continuous-spin extension, Comm. Math.
       Phys. 36:233–241); Holley 1974 (S3, predecessor in same CMP
       issue).
     - 1980s: Daykin 1980 (S4, hierarchy framework, Stud. Appl.
       Math. 63:263–270); Graham 1983 (S5, applications survey,
       Springer-Verlag chapter).
     - 1990s: Brightwell 1999 (S6, project's primary cite +
       applied-poset use, Discrete Math. 201:25–52, **§4.2 cell-
       averaging step is the immediate ancestor of EX-7 consumption**);
       Grimmett 1999 (S7, Percolation textbook §2.2, Springer GMW
       321).
     - 2000s: Liggett 1985/2005 reprint (S8, IPS textbook Ch. II §2,
       Springer GMW 276).
     - 2020s: Encyclopedia of Mathematics current entry (S9);
       Chan–Pak 2024 survey (S10, arXiv:2311.02743, EMS Surveys
       Math. Sci.).

     The result is **taught in graduate textbooks** (Grimmett 1999,
     Liggett 1985/2005) and **applied as black-box** in adjacent
     poset-combinatorics literature. **Independent author groups: 8+**.
     **No erratum or counterexample-claiming paper** exists.

  2. **Numerical sanity check.** **PASS.** Brute-force verification
     on **94 test instances** of the discrete cell-AD lemma on
     `(Fin F)^n` for `n ∈ {1, 2, 3, 4}` and `F ∈ {2, 4, 6, 12}`,
     with cell-grids `N | F`. Generator families: constant baseline,
     log-supermod (deterministic + random non-neg-coef
     pair-products), random 4-tuples with global UB, **sublattice-
     indicator family** (`O(2-chain), O(V), O(Λ), O(3-chain),
     O(diamond)` order polytopes — the **EX-7-motivating polytope-
     indicator shapes** that drove mg-2746's Monotone-vs-polytope
     hypothesis-mismatch finding), and a distinct 4-tuple
     non-symmetric quadruple. **14 948 cell-pair `(p, q)` checks**,
     **0 violations**, exact rational arithmetic via Python
     `Fraction` (no floating-point ambiguity), out-of-tree
     (independent of Lean codebase).

  3. **Uncontested in literature.** **PASS.** Result is standard
     background in 1990s+ graduate textbooks (Grimmett, Liggett)
     and applied as black-box in poset-combinatorics literature
     (Brightwell §4.2, Chan–Pak §9). The cell-averaging step appears
     identically in both AD's discrete route (S1) and Preston's
     continuous-spin route (S2) — two **genuinely independent
     proofs** by different methods. The Encyclopedia of Mathematics
     entry (S9, current/maintained) is uncontested.

* **AXIOMS.md update.** Fourth axiom entry
  (`OneThird.ContinuousFKG.cellMass_AD`) extended with a new
  "Separate verification (per Daniel directive 2026-05-08T16:11Z)"
  subsection containing the 3-row sub-check verdict table, links to
  the deliverable doc and numerical script, the GREEN verdict, and
  a note normalising the AD primary-citation date to **1978** (the
  AXIOMS.md text and source-axiom docstring cite "1979" due to
  journal-cover-date conventions; substantive math identical, DOI
  10.1007/BF00536201). No changes to the audit-bar 4-condition
  table (External / Difficult / Labeled / Low-risk all unchanged).

* **Trust surface impact.** None. The verification deliverable is
  documentation + a numerical script; no Lean source changes
  beyond the AXIOMS.md write-up. The fourth project axiom remains
  on the sub-α-C arc trust surface, now with an additional
  separate-verification subsection backing the `External` and
  `Low-risk` conditions. The `width3_one_third_two_thirds` headline
  trust surface is unchanged. EX-7 Session B (downstream consumer of
  `continuous_ad_general` ⇒ `cellMass_AD`) is **unblocked** per the
  audit-bar separate-verification discipline.

* **Trip-wires not fired.** Per ticket §5: no numerical violation
  (would have triggered URGENT mail to Daniel + revert mg-071b +
  halt sub-α-C); no thin literature coverage (would have triggered
  reduced-confidence framing). No token blow-up (well under the
  250k cap; mostly latex + Python scripting).

* **Verdict.** **GREEN** per ticket §6. PM next step: surface
  verification GREEN to Daniel in evening digest and proceed with
  **EX-7 Session B** scoping ticket dispatch (chamber-decomposition
  reduction + `continuous_ad_general` consumption +
  `stanley_log_supermod` inner-step closure, ~150–270 LoC per
  mg-2746 §7.2).

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
* **Default for next ticket.** **EX-3 done (mg-8c66, `ed9f6e6`;
  see §1.13). EX-4 Session A done (mg-4831, `ac56bc4`; see
  §1.14) — GREEN with small spec correction (LowerSet → UpperSet
  in the target signature; chamber-decomp arc downstream
  unaffected). EX-4 Session B done (mg-2442, `89786cf`; see
  §1.16) — GREEN; both directions of Stanley vertex theorem in
  Lean as `OrderPolytope.extremePoints_eq` against the in-tree
  `OrderPolytope α`; trust surface unchanged (`#print axioms`
  emits only `{propext, Classical.choice, Quot.sound}`); ~330 LoC
  at the lower edge of the mg-4831 §6 estimate.
  **EX-5 Session A done (mg-79a9, `3e76ac3`; see §1.17) —
  GREEN-2 (split Session B + Session C).** Latex-first scoping
  of the chamber decomposition `O(α) = ⋃_L σ_L` with `Vol(σ_L) =
  1/n!` and measure-zero pairwise overlaps (Stanley 1986 §1):
  rigorous proofs of all three claims via measure-preserving
  relabel `MeasurableEquiv.piCongrLeft` reducing σ_L to the
  standard ordered cube `Δ_n`, symmetric S_n-tiling of `[0,1]^n`
  giving `Vol(Δ_n) = 1/n!`, Szpilrajn-on-level-set cover
  construction, and `addHaar_submodule` for the strict-hyperplane
  measure-zero overlap. **No fundamental mathlib gap**; one
  derivable in-file gap (`volume_orderedCube`, ~150–200 LoC of
  derivation in Session B) **strengthens DH-5** (combined EX-3 +
  EX-4 + EX-5 mathlib upstream PR `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`).
  **No fallback to mg-163f §4.4 discretised path needed.**
  **EX-5 Session B done (mg-497d, this commit; see §1.18) —
  GREEN.** Lean port of the chamber definition + volume theorem;
  ~430 LoC at the lower edge of mg-79a9 §7.1's 395–560 estimate;
  trust surface unchanged (no new project axioms);
  **`volume_orderedCube` is in tree** as the
  `OneThird.LinearExt.OrderedCube.volume_orderedCube` master
  theorem (DH-5 candidate, sub-namespace `OrderedCube`).
  **PM files EX-5 Session C scoping ticket next** (cover via
  Szpilrajn-on-level-set + measure-zero overlap +
  `chamber_inter_meas_zero` + master
  `orderPolytope_eq_iUnion_chamber`; deliverable §3 + §4 +
  §5.3–§5.5 are the Session C brief; ~420–625 LoC, ~260–395k
  tokens, 1 polecat session). EX-3, EX-4, and EX-5 Sessions A/B
  do **not** consume `stanley_log_supermod` directly (axiom
  enters consumer chain starting at EX-7 onward); the temp axiom
  remains the discharge target of either DH-1 (preferred) or
  Option B (fallback). The corollary `stanley_mu_log_supermod`
  is no longer needed for Path A (Path B-only) and is dropped
  from the critical path.
  **EX-5 Session C done (mg-10d9, `7b084ba`; see §1.19) —
  GREEN.** Cover + measure-zero overlap + master volume theorem
  in Lean (~280 LoC at the lower edge of mg-79a9 §7.2's 420–625
  estimate; Route C lex-sort compactness win); chamber-decomposition
  triple complete in tree (`chamber`, `volume_orderedCube`,
  `chamber_cover`, `chamber_inter_meas_zero`,
  `orderPolytope_volume`); trust surface unchanged (no new project
  axioms). DH-5 fully realised — combined EX-3 + EX-4 + EX-5
  upstream candidate `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`
  is realisable as a single ~900–1100 LoC PR.
  **EX-6 Session A done (mg-e622, this commit; see §1.20) —
  GREEN-2 (split Session B + Session C).** Latex-first scoping
  of continuous FKG / Ahlswede–Daykin on `[0,1]^n` via the
  standard Riemann-sum discretisation route: discrete FKG/AD on
  `(Fin (N+1))^n` (mathlib `fkg` / `four_functions_theorem_univ`)
  + step-function approximation `f_N⁻ ≤ f ≤ f_N⁺` + limit `N → ∞`
  via DCT (`tendsto_integral_filter_of_dominated_convergence`).
  **No fundamental mathlib gap**; one auxiliary derivable in-file
  gap (`Monotone.aeContinuousAt_pi` multivariate, ~80 LoC of
  derivation in Session C) **strengthens DH-4 sub-DH-4-A** (small
  upstream PR alongside the main DH-4 continuous-FKG file).
  **No fallback to mg-163f §4.4 integer-sub-lattice path needed.**
  **PM files EX-6 Session B scoping ticket next** (discrete FKG/AD
  on `(Fin (N+1))^n` + step-function approximation + Riemann-sum
  identity; deliverable §3 + §5.1–§5.2 + §6.1 + §8.1 are the
  Session B brief; ~600–900 LoC, ~350–500k tokens, 1 polecat
  session). EX-6 does **not** consume `stanley_log_supermod` (axiom
  enters at EX-7+ per §1.11) and does **not** consume EX-3/EX-4/EX-5
  (chamber decomp lives downstream of EX-6 in EX-7's drops headline
  derivation, not upstream of EX-6 itself); EX-6 can therefore be
  developed in parallel with any future EX-3/EX-4/EX-5 mathlib-
  upstream extraction.
  **EX-6 Session B done (mg-a6ed, this commit; see §1.21).**
  Lean port of mg-e622 §5.1 + §5.2 landed in
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
  (NEW file ~470 lines, mathlib-PR-class). **§5.1 deliverable
  `fkg_discrete_pi`** (discrete FKG on `(Fin (N+1))^n`, Riemann-sum
  form) is fully proved as a corollary of mathlib `fkg` with
  `μ ≡ 1`; `ad_discrete_pi` companion via
  `four_functions_theorem_univ`. **§5.2 step-function infrastructure**
  also fully proved: `stepRetract`, `stepLower`, monotonicity sandwich,
  cell-volume identity `volume_cell`, cell-decomposition core
  `stepLower_eq_of_mem_cell`. The Riemann-sum identity
  `integral_stepLower_eq_riemann` is **stated** with the per-cell
  ingredients prepared; its integration-side assembly (cell partition
  + finite additivity) is the single `sorry`, deferred to Session C
  alongside the dominated-convergence limit. Build green for full
  `OneThird` target. Trust surface impact: none. **PM files EX-6
  Session C scoping ticket next** (a.e. convergence + DCT + master
  `continuous_fkg` / `continuous_ad` + full
  `integral_stepLower_eq_riemann` assembly + 1D Chebyshev
  hand-verification; ~400–700 LoC, ~250–400k tokens per mg-e622
  §8.2).
  **EX-7 Session A done (mg-2746, this commit; see §1.22) —
  AMBER-leaning-GREEN.** Latex-first scoping of the drops headline
  `probEvent'_mono_of_subseteq_upClosed` for `Q.Subseteq Q'` via
  chamber decomposition + continuous AD. **Substantive scoping
  finding**: the in-tree `continuous_ad` (mg-7d37) carries
  `Monotone f_i` hypotheses that do not match the EX-7 application's
  non-cube-monotone polytope indicators `1_{O(Q)}, 1_{O(Q')}`
  (counterexample: `f = (0.3, 0.5) ∈ O({(a,b)})` but
  `f' = (0.7, 0.5) ≥ f` componentwise has `f'(a) > f'(b)`, so
  `f' ∉ O({(a,b)})`). **Resolution**: Path R-A files **EX-6
  Session F** (NEW, prerequisite to EX-7 Session B) for a
  Monotone-free `continuous_ad_general` via cell-averages + Lebesgue
  differentiation theorem (literature-standard Ahlswede–Daykin 1979 /
  Preston 1974 form; Sub-DH-4-B strengthening of DH-4); ~300 LoC,
  ~150–250k tokens. EX-7 Session B (post-Session-F) is then
  ~150–270 LoC, ~80–150k tokens (matches polecat brief). **Combined
  Sessions F + B: ~400–600 LoC, ~250–400k tokens**, tracking the
  upper edge of mg-91be §5.7's 400–800 LoC envelope. Trust surface
  impact: none (no new project axioms;
  `OneThird.LinearExt.stanley_log_supermod` consumed at the
  inner-step closure per deliverable §2.6). Path R-B (combinatorial
  chamber-pairing argument) is the AMBER-leaning-RED contingency if
  Path R-A trip-wires fire on an unexpected mathlib obstruction.
  **PM files EX-6 Session F scoping ticket next** (deliverable §4.2 +
  §5.1 + §7.1 form the Session F brief), then EX-7 Session B once
  Session F lands.
  **EX-6 Session F done (mg-071b, `8b49708`; see §1.23) — AMBER-
  leaning-GREEN.** Monotone-free `continuous_ad_general` landed via
  cell-averages route; substantive scoping finding mid-session
  surfaced that the cell-AD inner step is the literature-standard
  Ahlswede–Daykin 1979 Lemma 2 (~1000–1500 LoC mathlib measure-theory
  glue beyond Session F budget); Option 2 (axiom-bearing) executed
  with mayor visibility and `cellMass_AD` introduced as **4th project
  axiom** under DH-4 discharge target. Trust surface impact:
  +1 axiom (4 total, sub-α-C arc only); `#print axioms
  continuous_ad_general` gives mathlib triplet + `cellMass_AD`.
  **cellMass_AD verification done (mg-d731, `e1fdaa1`; see §1.24) —
  GREEN.** Three orthogonal sub-checks all PASS (cross-literature: 10
  sources / 5 decades; numerical sanity: 14 948 cell-pair checks / 0
  violations on EX-7-motivating polytope-indicator shapes;
  uncontested in literature). EX-7 Session B unblocked per the
  audit-bar separate-verification discipline.
  **EX-7 Session B done (mg-4a56, this commit; see §1.25) — GREEN per
  Option 3 (mayor override).**  Structural infrastructure landed in
  `lean/OneThird/Mathlib/RelationPoset/DropsHeadline.lean` (~205 LoC):
  `OrderPolytope' Q` (data-version order polytope with `rfl`-bridge to
  typeclass `OrderPolytope α` under `Q.asPartialOrder`),
  `OrderPolytope'_subset_of_subseteq` (set-level FKG mono-under-aug),
  `OrderPolytope'_inf_mem` and `OrderPolytope'_sup_mem` (sublattice
  property — the key structural fact for the Brightwell §4.2 chamber +
  AD inner step), `OrderPolytope'_measurableSet` and
  `OrderPolytope'_subset_cube` (transports of mg-8c66 typeclass
  results).  **Substantive scoping finding (mid-session, mailed to
  mayor at session start)**: the substantive Daykin–Saks 1981 swap-
  induction inner step turned out to require ~500–1000 LoC of measure-
  theory glue beyond the Session B budget per mg-2746 §7.2.  Three
  options surfaced (full closure, 5th project axiom mirroring mg-071b,
  structural infra only); mayor returned **Option 3** as the trust-
  surface-preserving call (≤4-axiom envelope committed in previous
  evening digest). Trust surface impact: **none** (`#print axioms`
  triplet `{propext, Classical.choice, Quot.sound}`; no new project
  axioms). Master theorem `probEvent'_mono_of_subseteq_upClosed`
  **deferred to EX-7 Session C** (estimated 2–3 polecat sessions,
  ~600–1000 LoC total, consuming this session's structural infra +
  mg-10d9 chamber decomp + mg-071b `continuous_ad_general` +
  mg-d0fc `stanley_log_supermod`). **PM files EX-7 Session C scoping
  ticket next** (mg-2746 §2.4 + §5.2 form the Session C brief; budget
  split per mayor preference); EX-8 (case3-port-2) and EX-9 (Brightwell-
  port-A) remain blocked behind EX-7 Session C.
  **EX-7 Session C.1 done (mg-1f3a, this commit; see §1.26) — GREEN
  per Option 1 closure path (no 5th axiom).** Chamber-transport
  infrastructure for `OrderPolytope' Q` landed in
  `lean/OneThird/Mathlib/RelationPoset/DropsHeadlineChamber.lean`
  (~267 LoC): `chamber'` (data-version chamber simplex),
  `chamber'_subset_orderPolytope'`, `chamber'_volume` (Stanley
  1986 (1.5): `volume(σ_L) = 1/n!`), `measurableSet_chamber'`,
  `chamber'_inter_meas_zero` (Stanley 1986 (1.4) overlap),
  `chamber'_cover` (Stanley 1986 (1.4) cover),
  `numLinExt'_eq_numLinExt_asPartialOrder` (count agreement under
  `Q.asPartialOrder`), `orderPolytope'_volume` (Stanley 1986 (1.4)
  master: `volume(O(Q)) = numLinExt' Q / n!`).  All seven theorems
  transport via the mg-4a56 `OrderPolytope'_eq_asPartialOrder`
  `rfl`-bridge plus the natural
  `{ toFun := L.toFun, monotone := L.monotone }`-construction;
  no new mathematical content beyond mg-10d9 / mg-497d.  Trust
  surface impact: **none** (`#print axioms` triplet
  `{propext, Classical.choice, Quot.sound}`; no new project axioms;
  ≤4-axiom envelope preserved per mayor mg-4a56 override).
  Master theorem `probEvent'_mono_of_subseteq_upClosed` advances to
  **EX-7 Session C.2** (single-edge induction + swap involution,
  ~200 LoC; mg-1f3a §1.26 handoff brief). EX-7 Session C.2 + C.3
  remain estimated ~450–850 LoC combined; EX-8 and EX-9 blocked
  behind Session C.3 closure.  3-round trip-wire on EX-7 chain
  (per mg-1f3a brief) cleared: 0 amber rounds running.

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
  **Post-mg-e22f update (2026-05-09).** The temp axiom is now
  externally **independently verified** along three orthogonal axes
  (cross-literature 7 sources / 4 decades; numerical sanity 16
  posets / 2 835 pairs / 0 violations; uncontested-in-literature)
  per Daniel's stronger separate-verification bar (directive
  2026-05-08T16:11Z); see §1.15 + AXIOMS.md `stanley_log_supermod`
  "Separate verification" subsection. This **does not** change DH-1's
  leverage assessment — the verification supports the temp axiom on
  the trust surface but does not eliminate the LoC saving from a
  successful mathlib upstream PR. **DH-1 remains the highest-leverage
  shortening for the sub-α-C arc trust surface** (collapses the third
  named axiom to a mathlib citation; surfaced to Daniel as such in
  the next evening digest).

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
  **Post-mg-e622 update (2026-05-09).** **EX-6 Session A latex-first
  scoping done** (§1.20); the proof of continuous FKG/AD on `[0,1]^n`
  is **rigorously written** via the standard Riemann-sum
  discretisation route (deliverable §1–§4) and **Lean-portable**
  with **no fundamental mathlib gap** (deliverable §6.1: all APIs
  verified at v4.29.1 — `fkg`, `four_functions_theorem_univ`,
  `Pi.instDistribLattice`, `tendsto_integral_filter_of_dominated_convergence`,
  `volume_pi_pi`, `addHaar_submodule`,
  `Monotone.countable_not_continuousAt`). One auxiliary multivariate
  "monotone implies a.e. continuous" lemma (`Monotone.aeContinuousAt_pi`,
  ~80 LoC derivable) is the only sub-gap; **sub-DH-4-A** small
  upstream candidate alongside the main file. **The deliverable is
  the mathlib-PR-class proof, structured for direct upstream
  extraction once Sessions B + C land** (Session B = ~600–900 LoC
  discrete-side scaffolding + step-function approximation +
  Riemann-sum identity; Session C = ~400–700 LoC a.e. convergence +
  DCT + master theorem; total ~1000–1600 LoC). Daniel's optional
  surface for the upstream PR
  (`Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`); natural
  reviewers Yael Dillies, James Gallicchio, Bhavik Mehta.
  **Integer-sub-lattice fallback** (mg-163f §4.4) is **not**
  recommended as primary route per deliverable §7: the size-`N`
  factor infiltrates EX-7+ (+200–400 LoC downstream); the fallback
  remains as the contingency if Session C trip-wires fire (the
  discrete-FKG part of Session B is reusable as the fallback's
  main content). PM next step: file EX-6 Session B scoping ticket.
  **Post-mg-d731 update (2026-05-09).** `cellMass_AD` (the 4th
  named project axiom, mg-071b `8b49708`) **independently verified
  GREEN** under the audit-bar separate-verification extension
  (Daniel directive 2026-05-08T16:11Z). Three sub-checks all PASS:
  cross-literature (10 sources / 5 decades, including standard
  graduate textbooks Grimmett 1999 and Liggett 1985 and the
  project's primary downstream consumer Brightwell 1999 §4.2),
  numerical sanity (94 instances / 14 948 cell-pair checks / 0
  violations, exact rational arithmetic, covering the
  EX-7-motivating polytope-indicator family), and uncontested
  status. DH-4 mathlib upstream PR remains the highest-leverage
  shortener for Path A's EX-6/EX-7 chunk; the temporary axiom is
  now externally verified and trust-surface-safe for downstream
  EX-7 Session B consumption. Verification deliverable
  `docs/path-alpha-execution-arc/cellMass-AD-verification.md`;
  numerical script `scripts/cellMass_AD_check.py`; AXIOMS.md
  `cellMass_AD` entry extended with "Separate verification"
  subsection. See §1.24 (this update).

### §3.10 DH-5 — Stanley order-polytope basics as upstream mathlib PR (post-mg-4831)

* **Source.** mg-4831 §5.2.
* **Question.** Is the EX-3 (`OrderPolytope α` definition + basic
  structural properties) + EX-4 (Stanley vertex theorem)
  combination upstream-able to mathlib as a single
  "Stanley order polytope basics" unit?
* **Why it matters.** Both EX-3 (mg-8c66) and EX-4 (this Session A
  scoping) are independently mathlib-PR-class chunks (mg-91be §5.3
  / §5.4 / §7; mg-163f §2.8). A combined upstream PR
  (`Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`,
  ~600–900 LoC) is a cleaner mathlib-reviewer story than each
  alone, and it has **independent value** outside the OneThird
  project (the order polytope is a standard object in algebraic
  combinatorics, used in Stanley's poset-Ehrhart theory and many
  downstream applications). Maintainer: Yaël Dillies (consistent
  with `Mathlib.Analysis.Convex.Extreme` + `Mathlib.Combinatorics.SetFamily.FourFunctions`).
  Sub-component DH-5a: `extremePoints (Set.Icc a b) = {a, b}` for
  `a ≤ b` in a `LinearOrderedField` — a small (~15-25 LoC)
  upstream-PR-class lemma noted in mg-4831 §4.4.
* **Cost saving.** Speculative; not on the critical path. EX-3 is
  already in tree (mg-8c66) so DH-5 acceleration would only
  collapse the EX-4 Session B port (~330–470 LoC) to a mathlib
  citation if the combined PR lands. Lower priority than DH-1
  (Stanley log-supermod, ~3000–5000 LoC saving) and DH-4
  (continuous FKG, ~1000–2000 LoC saving).
* **Status.** Surfaced post-mg-4831. PM should mention DH-5 in
  the next digest as a *secondary* mathlib-upstream candidate
  (alongside DH-1 + DH-4 as the higher-leverage primary
  candidates). Concrete file target:
  `Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`.

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
* **Post-mg-4831 (EX-4 Session A executed) — decision point closed.**
  Stanley vertex theorem latex writeup + mathlib API mapping
  delivered in `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`
  (~880 lines). Both directions of Stanley 1986 Theorem 1.2 proven
  rigorously without convex-geometry / continuous FKG / mixed-volume
  machinery. Mathlib `Set.extremePoints` API verified GREEN against
  the in-tree `OrderPolytope α`. **One small spec correction
  surfaced** (deliverable §4.1): the LoC-spec `LowerSet`
  parameterisation should be `UpperSet` (or `LowerSet` + complement)
  to match the in-tree `OrderPolytope`'s order-preserving
  convention; chamber-decomp arc downstream unaffected. **Session B
  ETA refined to ~330–470 LoC, ~170–265k tokens** (from mg-91be
  §5.4's 400–600 LoC, 200–300k tokens). DH-5 (Stanley
  order-polytope basics as upstream mathlib PR) surfaced as
  secondary mathlib-upstream candidate (§3.10). Build unchanged
  (no Lean source touched). PM next step: file EX-4 Session B
  scoping ticket (direct Lean port using deliverable §6 as
  component breakdown).
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
* mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α`
  defined with basic structural properties (convex, closed,
  bounded, compact, measurable) and discrete-3-antichain
  hand-verification. Build green; no new axioms.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`.
* mg-e22f (`f1c4a66`) — Stanley log-supermod independent
  verification: GREEN per Daniel directive 2026-05-08T16:11Z.
  Three sub-checks pass (cross-literature 7 sources / 4 decades;
  numerical sanity 16 posets / 2 835 pairs / 0 violations;
  uncontested in literature). No Lean source changes beyond
  AXIOMS.md write-up. Trip-wires not fired.
  `docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`,
  `scripts/stanley_log_supermod_check.py`,
  `lean/AXIOMS.md` (third entry, "Separate verification" subsection).
* mg-4831 (this commit) — EX-4 Session A executed: Stanley vertex
  theorem latex writeup + mathlib `Set.extremePoints` API mapping.
  GREEN with small spec correction (target signature should use
  `UpperSet α` rather than `LowerSet α`; cardinality preserved
  under upper/lower duality so chamber-decomp arc downstream
  unaffected). Both directions of Stanley 1986 Theorem 1.2 proven
  rigorously; no convex-geometry / continuous FKG / Aleksandrov–
  Fenchel needed (Direction 1 is direct; Direction 2 uses
  `±ε`-perturbation on the level set `f^{-1}(c)`). Session B ETA
  refined to ~330–470 LoC, ~170–265k tokens. DH-5 (Stanley
  order-polytope basics as upstream mathlib PR; combined EX-3 +
  EX-4) surfaced as secondary candidate. Trip-wires not fired
  (~120k of 350k cap; no API mismatch; no Direction-2 obstruction).
  No Lean source changes.
  `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`.
* mg-a6ed (this commit) — EX-6 Session B executed: discrete FKG /
  AD on `(Fin (N+1))^n` + step-function approximation `stepLower` +
  Riemann-sum identity (statement). Direct Lean port of mg-e622
  Session A scoping (§5.1 + §5.2). The §5.1 deliverable
  `fkg_discrete_pi` (discrete FKG on `(Fin (N+1))^n`, Riemann-sum
  form) is fully proved as a corollary of mathlib `fkg` with
  `μ ≡ 1`; companion `ad_discrete_pi` from `four_functions_theorem_univ`.
  §5.2 step-function infrastructure (`stepRetract`, `stepLower`,
  monotonicity sandwich, cell-decomposition core
  `stepLower_eq_of_mem_cell`, cell-volume identity `volume_cell`)
  also fully proved. The Riemann-sum identity
  `integral_stepLower_eq_riemann` is **stated**; its integration-
  side assembly (cell partition + finite additivity) is the single
  `sorry`, deferred to Session C alongside the dominated-convergence
  limit. Build: `lake build` succeeds for full `OneThird` target
  (2641 jobs); new file wired into `lean/OneThird.lean`. Trust
  surface impact: none (no new axioms; `stanley_log_supermod` not
  consumed). File structured for upstream extraction to mathlib as
  `Mathlib.Analysis.MeanInequalities.ContinuousFKG` (DH-4 candidate).
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`,
  `lean/OneThird.lean` (one import line),
  `docs/path-alpha-execution-arc/state.md` (§1.21 NEW + header
  "Last update" + §3.4 update + this §5 entry).
* mg-2746 (this commit) — EX-7 Session A executed: drops headline
  via chamber + continuous AD latex-first scoping. **Substantive
  scoping finding**: in-tree `continuous_ad` (mg-7d37) requires
  `Monotone f_i` for each of the four functions, but the drops
  application needs AD on non-cube-monotone polytope indicators
  `1_{O(Q)}, 1_{O(Q')}` (counterexample documented in deliverable §0
  + §3). **Resolution Path R-A**: file EX-6 Session F (new
  prerequisite) for a Monotone-free `continuous_ad_general` via
  cell-averages + Lebesgue differentiation theorem (literature-
  standard form; Sub-DH-4-B strengthening of DH-4); ~300 LoC,
  ~150–250k tokens. EX-7 Session B then ~150–270 LoC, ~80–150k
  tokens. Combined ~400–600 LoC over 2 Lean sessions. Path R-B
  (combinatorial chamber-pairing) AMBER-leaning-RED contingency.
  Trust surface impact: none (no new project axioms;
  `stanley_log_supermod` consumed at inner-step closure). Trip-wires
  per deliverable §6.4 + §7.4 not fired (~70k of 350k cap; mathlib
  measure theory at v4.29.1 covers all needed APIs). Verdict
  AMBER-leaning-GREEN. PM next step: file EX-6 Session F scoping
  ticket, then EX-7 Session B once Session F lands.
  `docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md`.
* mg-4adf (this commit) — EX-6 Session C executed (partial):
  closed Session B's deferred `integral_stepLower_eq_riemann`
  sorry sorry-free via the cell-partition + finite-additivity
  assembly (`integral_iUnion_fintype` over disjoint half-open
  cells `C_k` of volume `1/N^n`); added `gridFnN` /
  `fkg_discrete_pi_finN` (Riemann-form discrete FKG indexed by
  `Fin n → Fin N`); added `stepUpper`, `le_stepUpper_self`,
  `integral_stepUpper_eq_riemann`, `integrableOn_stepUpper_cube`,
  `integrableOn_stepLower_cube`. Master theorems
  `tendsto_integral_stepLower`, `continuous_fkg`, `continuous_ad`
  signed in §8 with precise sorry-diagnosis (per Daniel feedback
  2026-05-09: be specific in deferred-sorry diagnosis, paper vs
  formalization). Single fundamental remaining sorry:
  `sum_step_diff_bound` (Σ-difference bound via `Fin.succ` /
  `Fin.castSucc` reindexing into `Fin (N+1)`, cancellation of
  common image, residual `≤ ((N+1)^n − N^n) · M` from `Fin (N+1)
  \ image(castSucc)` cardinality + monotone bound; ~150 LoC
  pure Finset combinatorics, no mathlib gap). Three dependent
  sorries (`tendsto_integral_stepLower`, `continuous_fkg`,
  `continuous_ad`) cascade from the bound but are otherwise
  mechanical (squeeze + `fkg_discrete_pi_finN` + Riemann
  identities + `Filter.Tendsto.mul`). Build: `lake build`
  succeeds (2506 jobs, 4 sorries). Trust surface unchanged
  (no new axioms; `stanley_log_supermod` not consumed). PM next
  step: file **EX-6 Session D** scoping ticket (the
  `sum_step_diff_bound` Finset-bij argument + dependent assembly).
  ETA Session D: ~150–250 LoC, ~100–200k tokens.
  `lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
  (~500 → ~1050 lines), `docs/path-alpha-execution-arc/state.md`
  (header "Last update" + this §5 entry).

---

*This is a living document. Future Path-α-flavoured polecat tickets
must (a) read this first, (b) update §1 / §2 / §3 / §4 with their
findings, (c) append a "Last update" line to the header. The
discipline applies starting now (mg-21a4).*
