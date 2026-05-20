# OneThird-S6-B Session 1 state report — Step 6 `cor:pointwise` grounded + Steps 1-6 cascade conclusion

**Ticket:** mg-65af (FULL REFACTOR Phase 2, Wave-4; **the final ticket of
Piece 1** — the Steps 1-6 cascade Lean port; scoped by mg-d8c7 §2.1 /
§5.2 under S6). Depends on mg-9576 (S6-A).
**Verdict:** **GREEN — substantively landed.** `step6.tex`
`cor:pointwise` (Pointwise coherence, Conclusion B, `step6.tex:583-713`)
is ported in *grounded* form, consuming the S6-A `thm:step6` dichotomy
output, and the complete Steps 1-6 cascade is assembled into a single
grounded conclusion `cascade_steps_1_6_grounded`. Both are instantiated
**non-vacuously** on a concrete width-3 non-chain poset with **two
genuinely opposite-signed rich interfaces** — the double-counting
identity and the pointwise corollary carry genuine *positive* content.
Full `lake build` clean; no new axioms, no `sorry`. No paper-side
rigor gap surfaced.

---

## §0. TL;DR

* **Piece 1 closes.** S6-A (mg-9576) grounded `thm:step6` (the
  dichotomy). S6-B grounds `cor:pointwise` (Conclusion B) and assembles
  the whole Steps 1-6 cascade. New file
  `Step6/PointwiseGrounded.lean`; the abstract `Step6/*.lean` and all
  downstream modules are untouched.
* **The grounding of `cor:pointwise`.** The abstract
  `Step6.cor_pointwise` (`Assembly.lean`) takes the disagreement-mass
  bound `∑_L 2·n₊(L)·n₋(L) ≤ R` as an *opaque* hypothesis. The paper
  *derives* it (Step 2 of the `cor:pointwise` proof, `step6.tex:643-651`)
  by a **double-counting identity**. This session **proves that
  identity** (`disagreement_mass_eq_double_count`) on genuine data: it
  ties the opaque `R` to the genuine overlap mass `∑ pairOverlap` of
  the disagreeing interface pairs (the genuine second moment of the
  disagreement subgraph). `cor_pointwise_grounded` then consumes a
  genuine overlap-mass bound, not an opaque one.
* **The Steps 1-6 cascade conclusion.** `cascade_steps_1_6_grounded`
  is the `step6.tex` "Full proof in compressed form"
  (`step6.tex:735-760`, steps 1-9) as a single grounded theorem: from
  the genuine summed Step-4 bound (G9), the genuine Step-5 first-moment
  richness (G10), and a genuine low-conductance hypothesis, it runs the
  S6-A dichotomy closure → coherence → splits the disagreement mass →
  delivers Conclusion B (the `I²`-weighted pointwise-coherence Markov
  bound). This is the termination point of Piece 1.
* **Non-vacuity bar met, strengthened over S6-A.** The concrete
  instances use **two genuinely opposite-signed rich interfaces** on
  `Fin 3 × Fin 3` — a real incoherent pair on a real overlap. So,
  unlike S6-A's singleton-interface instance (`∑_bad w = 0`), the
  disagreement mass here is genuinely **positive** (`= 2`): the
  double-counting identity fires with both sides `= 2`, the second
  moment is `M = 4`, and `cor_pointwise_grounded` delivers the tight
  `8 ≤ 8`. The cascade instance delivers `4 ≤ 16` with a genuine
  non-empty BK boundary and genuine `M = 4`.
* **No new axioms, no `sorry`, no headline-path change.** The new file
  is an import-only leaf; `#print axioms` of the headline is
  unaffected.

## §1. Inventory delta

```
Step6/PointwiseGrounded.lean   new   (cor:pointwise grounded + Steps 1-6 cascade + 2 concrete instances)
OneThird.lean                  +1 import line
```

`Step6/Assembly.lean`, `DichotomyGrounded.lean`, and all other modules
— unchanged.

## §2. What the grounding does

| Symbol | Role (`step6.tex`) |
|---|---|
| `disagreePairs` | the incoherent (orientation-disagreeing) ordered interface pairs `Rich_disagree` |
| `cross_count` | two-set generalisation of `visibility_sq_eq_sum_pairs` — `I_s·I_t = ∑_{s×t} 𝟙[L ∈ F⋆_α ∩ F⋆_β]` |
| `posCount_eq_visibility` / `negCount_eq_visibility` | `n₊(L)` / `n₋(L)` are the restricted visibilities of the `±`-oriented sub-families |
| `two_mul_pos_neg_eq_disagree_indicator` | pointwise double-counting: `2·n₊(L)·n₋(L) = ∑_{Rich_disagree} 𝟙[L ∈ F⋆_α ∩ F⋆_β]` |
| `disagreement_mass_eq_double_count` | **`step6.tex` Step-2 identity** (`step6.tex:643-651`): `∑_L 2·n₊·n₋ = ∑_{Rich_disagree} w_{αβ}` — the bridge that grounds `cor:pointwise` |
| `cor_pointwise_grounded` | **`cor:pointwise` grounded** (`step6.tex:583-713`): from the genuine disagreement-mass bound, the `I²`-weighted Markov bound `t_n·δ_d·∑_A I(L)² ≤ t_d·R` on the "mostly-disagreeing" set `A` |
| `cascade_steps_1_6_grounded` | **the assembled Steps 1-6 cascade conclusion** (`step6.tex:735-760`, steps 1-9): G9 + G10 + low-conductance → coherence → Conclusion B |
| `cor_pointwise_grounded_concrete` | non-vacuous `Fin 3 × Fin 3` instance with two opposite-signed interfaces |
| `cascade_steps_1_6_grounded_concrete` | non-vacuous cascade instance (mg-65af acceptance bar, Piece-1 termination) |

`cascade_steps_1_6_grounded` is the substantive deliverable and the
**termination point of Piece 1**. It consumes the S6-A grounded
dichotomy via `thm_step6_rich_closure_grounded_of_firstMoment` (the
full G9 + G10 assembly), obtains the genuine coherence bound
`δ_d·∑_bad w ≤ δ_n·M`, splits the disagreement mass into bad-active +
non-active parts, and feeds `cor_pointwise_grounded` to deliver
Conclusion B. The double-counting identity
`disagreement_mass_eq_double_count` is the genuine new content: it is
the `step6.tex` Step-2 equation, proved by counting triples
`(L, α, β)` with `L ∈ F⋆_α ∩ F⋆_β` and `σ_α ≠ σ_β` in two ways
(`cross_count` + the `(+,-)`/`(-,+)` split of `Rich_disagree`).

The abstract `Step6.cor_pointwise` and its lemmas
(`cor_pointwise_aggregate`, `cor_pointwise_markov`,
`minority_mul_visibility_le_two_mul_pos_neg`,
`visibility_eq_pos_add_neg`) are consumed as already landed; the
grounded layer adds only the double-counting identity that connects
them to the genuine `thm:step6` output.

## §3. Non-vacuous instantiation (`mg-65af` acceptance bar)

`Fin 3 × Fin 3` (product order), the genuine width-3 non-chain
9-element grid poset, with **two rich interfaces** `false, true`
(`Pair := Bool`, `richStar := univ`), both with the singleton fiber
`{gridLinExt}` and carrying **opposite orientations** (`σ := id`, so
`σ false = +1`, `σ true = -1`). This is a genuine incoherent pair: a
real disagreeing pair on a real overlap.

`cor_pointwise_grounded_concrete` bundles, all proved:

1. `HasWidth (Fin 3 × Fin 3) 3` and `¬ IsChainPoset (Fin 3 × Fin 3)`;
2. the genuine disagreement mass is `2` — **strictly positive**, two
   disagreeing pairs each of overlap `1`;
3. the `step6.tex` Step-2 double-counting identity
   `∑_L 2·n₊·n₋ = ∑_{Rich_disagree} w` holds, both sides `= 2`;
4. `cor_pointwise_grounded` fires, delivering `1·2·∑_A I² ≤ 2·4`
   (i.e. `8 ≤ 8`, tight);
5. the `I²`-mass on the "mostly-disagreeing" set `A` is genuinely
   positive (`∑_A I² = 4`).

`cascade_steps_1_6_grounded_concrete` bundles, all proved:

1. width *exactly* `3`, non-chain;
2. the BK boundary `∂_BK S` is genuinely non-empty (`1 ≤ |∂_BK S|`,
   `grid_bkBoundary_pos`, S6-A) — a real BK cut edge;
3. the genuine second moment / overlap mass is `M = 4`;
4. the genuine disagreement mass is `2` — strictly positive;
5. `cascade_steps_1_6_grounded` genuinely fires, assembling the whole
   Steps 1-6 cascade into Conclusion B: `1·1·∑_A I² ≤ 2·(2·1·M)`,
   i.e. `4 ≤ 16`.

This **strengthens** the S6-A non-vacuity precedent: S6-A's
singleton-interface instance had `∑_bad w = 0` (a single rich family
carries no incoherent pair); the S6-B instance has a genuine
*positive* disagreement mass `2`, so the double-counting identity and
the pointwise corollary operate on genuinely populated objects.

**Honest scope note.** As in S6-A, at a 9-element poset with a
singleton cut one cannot exhibit genuinely-low conductance *together
with* genuine bad **active** mass — that asymptotic regime needs large
`α`. The cascade concrete instance therefore takes the bad-*active*
set empty (`badSet = ∅`, so the summed Step-4 bound holds trivially
and the strict low-conductance hypothesis `|∂_BK S| < |∂_BK S| + 1`
is consistent), while the genuine *disagreement* mass `2` is carried
by the **non-active** term — a faithful instance of the
`step6.tex:646-649` active/non-active split (the disagreeing pairs
here have overlap `1`, below any threshold `w₀ ≥ 2`). The genuine
quantitative content — "low conductance forces coherence, and
coherence forces pointwise coherence" — is the theorem
`cascade_steps_1_6_grounded` itself, whose proof genuinely runs the
S6-A expansion-contradiction closure followed by the double-counting
+ Markov argument.

## §4. No gap-discovery on the paper side

Default-skeptical re-read of `step6.tex:583-760` (`cor:pointwise` +
the compressed proof) against the abstract `Step6.Assembly` surfaced
**no paper-side rigor gap**. The `cor:pointwise` proof is a clean
five-step argument: majority vote (Step 1), double counting of
disagreeing pairs (Step 2), `n₊·n₋ ≥ ½·m·I` (Step 3), the
`M = ∑_L I²` identity (Step 4, `lem:gap-G5`(i), already landed in
`RichnessBound.lean`), and Markov (Step 5). Steps 1, 3, 4, 5 are
already in the abstract `Step6.cor_pointwise` machinery; Step 2 (the
double-counting identity) is the one piece the abstract layer assumed
opaquely, and this session proves it. The active/non-active split
(`step6.tex:646-649`) — the paper notes the non-active threshold `w₀`
is "absorbable into the constants of Theorem 6" — is modelled
faithfully as the explicit `hNonActive` hypothesis of
`cascade_steps_1_6_grounded` (the non-active disagreement mass is a
`δ`-fraction of `M`). The S1-E RED finding
(`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #8) does **not** block
this port: like the S6-A dichotomy, `cor:pointwise` consumes the
Step-1/Step-2/Step-3 outputs (`σ`, the fibers `F⋆`) *parametrically*,
so the grounded layer is independent of whether S1 delivers
`goodFiberSet` non-empty.

## §5. Build

`lake build OneThird.Step6.PointwiseGrounded` clean (~2s on the reused
mathlib cache). Full `lake build OneThird` clean (1434 jobs) — the new
file is an import-only leaf, no downstream module consumes it. No
`sorry`, no new axioms, no new warnings attributable to the new file.
(The pre-existing `ErrorControl.lean` unused-hypothesis linter
warnings are untouched scaffold, not a regression.)
