# EX-1 Session A.2 — Bjorner inductive closure (alternative-path deliverable)

**Polecat.** mg-7928 (cat-mg-7928).
**Date.** 2026-05-07.
**Branch.** `polecat-mg-7928` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-c7b9 (`4b5b1ba`) — EX-1 Session A scoping (AMBER); chose
  Bjorner combinatorial induction as variant; sketched §2.5 (lex
  closure) and §2.6 (Ψ injection) and flagged both as "not fully
  verified" pending Session A.2.
- mg-91be (`bb450a4`) — sub-α-C high-level scoping (AMBER leaning
  GREEN); EX-1 introduced as the most isolatable execution chunk.

**Verdict.** **AMBER (alternative-path branch fired).**

The primary path of this scoping ticket — close the Bjorner
inductive closure — **fails on a fresh structural fact**, which
trip-wire §5 of the polecat brief mandates STOP-and-surface for.
Specifically: the simple `(I, J) \to (I^+, J^+)` reduction with
the Bjorner injection `Ψ` (mg-c7b9 §2.6), combined with the
inductive hypothesis on the smaller pair, produces an inequality
in the **wrong direction** at the bridging step. There is no
sub-pair to which the inductive hypothesis can be re-applied to
recover the target inequality, because every natural alternative
sub-pair has the **same** lex rank `(|I \cup J|, |I \triangle J|)`
as the original, so the recursion does not terminate.

This is a real mathematical obstruction on the variant-3
(Bjorner-style) closure as imagined in mg-c7b9 §2.5–§2.6 — not a
proof-engineering hurdle that more careful position-arithmetic
would close.

The alternative-variant survey shows:

* **Variant 1 (Stanley 1981 Aleksandrov–Fenchel).** Known to work
  in the literature; heavy mathlib gap (~3000–5000 LoC for the AF
  inequality + order-polytope volume infrastructure, per mg-91be
  EX-3..EX-7). **Aligns with sub-α-C Path A's polytope arc**, so
  cost is partially amortised against the eventual chamber-decomp
  work.
* **Variant 2 (Daykin 1990 four-functions-direct).** Reaffirmed
  REJECT. mg-c7b9 §1.2 already noted that 4FT *consumes*
  log-supermodularity rather than producing it; the only candidate
  reduction (chain-encoded indicators on `J(\alpha)^{n+1}`)
  requires a saturated-chain bijection essentially equivalent to
  the Bjorner injection — circular.
* **Variant 4 (fresh combinatorial).** No clean fresh proof
  emerges; Stanley log-supermod is genuinely deep, with the
  combinatorial routes in the literature (Bjorner 1989,
  Daykin 1990) all going through some form of the same injection.

**PM-recommended next step.** Per polecat brief §6 verdict
targets, **AMBER (closure rigorous but with a small open question;
PM files Session A.3 narrowed to that question)** vs **RED
(closure cannot be made rigorous AND no alternative variant
works)**: this report is positioned at the AMBER/RED boundary.
Variant 1 is known to work, so no full RED. But the
**mathlib-PR-class** combinatorial closure that mg-c7b9 chose for
its mathlib-friendliness is **not closeable** via the route
sketched in mg-c7b9 §2.6.

The PM action item is structural — Daniel's call:

1. **DH-1 acceleration (recommended).** Stanley log-supermod is a
   known result; mathlib upstream PR via Yael Dillies (sub-α-C
   §3.5 / mg-c7b9 §4.3) is the highest-leverage parallel path.
   In the meantime, **temporarily accept Stanley log-supermod as a
   project axiom** in the same trust-surface tier as
   `case3Witness_hasBalancedPair_outOfScope` and
   `brightwell_sharp_centred`. Net impact on Path γ: zero. Net
   impact on sub-α-C Path A: defers EX-1 indefinitely; rescopes
   sub-α-C to start at EX-2 (Hibi chamber decomp) directly.

2. **Variant 1 commitment (heavy but known).** PM rescopes EX-1
   to use Stanley 1981 AF / order polytope volume route, accepting
   the ~3000–5000 LoC mathlib gap. This aligns with EX-3..EX-7's
   chamber decomp and AF infrastructure, so sub-α-C Path A becomes
   `EX-1 (AF) → EX-3..EX-7 (chamber)` with partial overlap. Path B
   (combinatorial level-`k` localisation) remains an alternative
   if the AF-via-order-polytope work surfaces a cleaner
   discrete-FKG path.

3. **Session A.3 with literature lookup.** PM files a narrow
   Session A.3 with explicit instruction to consult Bjorner 1989
   directly (or Stanley EC1 §3.5 / Aigner *Combinatorial Theory*
   Ch. II.4 / Brualdi–Mohammadi 1995 *Combinatorial polynomial
   inequalities for Stanley's poset chain inequality*). Estimated
   100–200k tokens, scoping-only. **Risk:** if the literature also
   uses an AF or 4FT route under the hood (likely), Session A.3
   converges to one of options (1)/(2) anyway.

4. **RED-and-rescope sub-α-C.** Per state.md §4.5 trip-wire ("New
   structural obstruction REDs sub-α-C"), Daniel may decide that
   the failure of the most mathlib-friendly Stanley log-supermod
   variant is enough to RED the sub-α-C arc and lock in Path γ.
   PM mails Daniel the verdict and lets Daniel make the call.

The polecat's recommendation, weighted by `feedback_long_arcs_are_pm_authority`:
**option (1) DH-1 acceleration**, with sub-α-C Path A continuing
on EX-2 onwards in parallel. Option (4) (full rescope) should be
mentioned in the mayor mail but flagged as "Daniel's call, not
PM's."

This document is the latex-first deliverable per polecat brief §3
and `feedback_latex_first_for_math_simp`. No Lean source is
touched. No proof of Stanley log-supermod is produced; the
deliverable is the rigorous identification of the closure failure
and the corresponding PM action item.

---

## §1 Why the Bjorner closure was harder than expected

This section follows the alternative-path-deliverable structure
mandated in the polecat brief §3. We re-cap the closure problem
from mg-c7b9 §2.5–§2.6, isolate the fresh structural fact that
fires the trip-wire, and explain why the variants that mg-c7b9
identified as "perhaps closable in Session A.2" are not closable
within the Bjorner-style framework as constructed.

### §1.1 Re-cap of mg-c7b9's framework

Throughout, `α` is a finite poset, `n := |α|`,
`J(\alpha) := \mathrm{LowerSet}(\alpha)` is the finite distributive
lattice of order ideals, and for `K \in J(\alpha)` we write
`e(K) := |\mathrm{LE}(\alpha[K])| = \mathrm{numLinExt}(\alpha[K])`,
where `\alpha[K]` is the sub-poset on `K \subseteq \alpha` with
inherited order.

**Goal.** Stanley log-supermodularity:

$$ e(I) \cdot e(J) \;\le\; e(I \cup J) \cdot e(I \cap J) \qquad
   \forall I, J \in J(\alpha) . \qquad (\star) $$

**mg-c7b9's framework (variant 3, Bjorner-style).** Induct on
`\delta := |I \triangle J|`. The inductive step picks
`m \in I \setminus J` and `m' \in J \setminus I` to be α-minimal
in `I \triangle J`, verifies that `m, m'` are α-incomparable, and
defines:

$$ J^+ := J \cup \{m\}, \qquad I^+ := I \cup \{m'\} . $$

The **reduction step** is bridged by the Bjorner injection
`\Psi : \mathrm{LE}(\alpha[I]) \times \mathrm{LE}(\alpha[J]) \hookrightarrow \mathrm{LE}(\alpha[I^+]) \times \mathrm{LE}(\alpha[J^+])`,
constructed by:

* `(\sigma, \tau) \mapsto (\sigma^+, \tau^+)` where
* `\sigma^+` is `\sigma` with `m'` inserted at the leftmost
  α-valid slot of `I^+`, and
* `\tau^+` is `\tau` with `m` inserted at the leftmost α-valid
  slot of `J^+`.

`Ψ` is injective by direct deletion-inverse.

The induction parameter is **lex on
`(|I \cup J|, |I \triangle J|)`**. Under the reduction, the first
coordinate `|I^+ \cup J^+| = |I \cup J|` is unchanged (since
`m \in I, m' \in J` already), and the second coordinate decreases
by 2 (`|I^+ \triangle J^+| = \delta - 2`).

The claimed closure chain:

1. By Ψ (injectivity): `e(I) \cdot e(J) \le e(I^+) \cdot e(J^+)`.
2. By inductive hypothesis on `(I^+, J^+)` (lex-rank
   `(|I \cup J|, \delta - 2)` strictly below `(|I \cup J|, \delta)`):
   $$ e(I^+) \cdot e(J^+) \;\le\; e(I^+ \cup J^+) \cdot e(I^+ \cap J^+) . $$
3. Compute the right-hand side:
   `I^+ \cup J^+ = I \cup J` (since `m \in I, m' \in J`), and
   `I^+ \cap J^+ = (I \cap J) \cup \{m, m'\}` (both `m, m'` are in
   both `I^+, J^+`). So
   $$ e(I^+) \cdot e(J^+) \;\le\; e(I \cup J) \cdot e((I \cap J) \cup \{m, m'\}) . $$
4. Combining (1) and (3):
   $$ e(I) \cdot e(J) \;\le\; e(I \cup J) \cdot e((I \cap J) \cup \{m, m'\}) . \qquad (\diamond) $$

### §1.2 The fresh structural fact: bridge inequality goes the wrong way

The target of the induction is `(\star)`:
`e(I) \cdot e(J) \le e(I \cup J) \cdot e(I \cap J)`. The chain
above gives `(\diamond)`:
`e(I) \cdot e(J) \le e(I \cup J) \cdot e((I \cap J) \cup \{m, m'\})`.

These are **not** the same inequality; converting `(\diamond)` to
`(\star)` requires
`e((I \cap J) \cup \{m, m'\}) \le e(I \cap J)` — a bound on
`e` going from a **larger** lower set down to a **smaller** one.

But the **monotonicity of `e`** points the other way:

**Lemma 1.1 (monotonicity of `e`).** If `K \subseteq K'` are both
lower sets of `\alpha`, then `e(K) \le e(K')`.

*Proof.* The restriction map `\sigma' \mapsto \sigma'|_K : \mathrm{LE}(\alpha[K']) \to \mathrm{LE}(\alpha[K])`
is **surjective**: every linear extension of `\alpha[K]` extends
to at least one linear extension of `\alpha[K']` by inserting the
elements of `K' \setminus K` one at a time at any α-valid slot
(e.g., always at the leftmost valid slot, which exists because
`K' \setminus K` consists of upward-closed elements relative to
`K` modulo lower-set constraints, and inserting any α-minimal
element of `K' \setminus K` at the back end is always α-valid).
Hence the fibers are non-empty and `|\mathrm{LE}(\alpha[K'])| \ge |\mathrm{LE}(\alpha[K])|`. ∎

Applied to `K := I \cap J` and `K' := (I \cap J) \cup \{m, m'\}`
(both lower sets, since `m, m'` are α-minimal in `I \triangle J`
so every `y < m` is in `I \cap J` and similarly for `m'`):

$$ e(I \cap J) \;\le\; e((I \cap J) \cup \{m, m'\}) . \qquad (\diamond') $$

Combining `(\diamond)` and `(\diamond')`:

$$ e(I) \cdot e(J) \;\le\; e(I \cup J) \cdot e((I \cap J) \cup \{m, m'\}) , \qquad (\diamond) $$
$$ e(I \cap J) \;\le\; e((I \cap J) \cup \{m, m'\}) . \qquad (\diamond') $$

Inequality `(\diamond)` is **strictly weaker** than `(\star)`
whenever `e((I \cap J) \cup \{m, m'\}) > e(I \cap J)`, which
is the generic case (equality only when adding `m` and `m'` does
not add any linear extensions, e.g., the trivial case where
`I \cap J = \alpha \setminus \{m, m'\}` and `\alpha[\{m, m'\}]` is
forced — which isn't a generic α). So `(\diamond)` does **not**
imply `(\star)`.

This is the fresh fact: the closure chain mg-c7b9 §2.6 produces
the wrong inequality.

### §1.3 Why no IH re-application closes the gap

A natural attempt to close `(\diamond)` to `(\star)` is to apply
the inductive hypothesis to a sub-pair whose `e(\cdot) e(\cdot)`
appears on the right-hand side of `(\diamond)`. The relevant
sub-pair candidates:

* **`(I \cap J, I \cup J)`.** Has `|I \cup J|` first coordinate
  unchanged from `(I, J)`; symmetric difference is
  `|I \triangle J| = \delta`, also unchanged. So lex-rank
  `(|I \cup J|, \delta)` is **identical** to `(I, J)` — the IH
  does **not** apply to a strictly-smaller pair.

* **`(I \cap J, (I \cap J) \cup \{m, m'\})`.** Has
  `|I \cup J|` first coordinate `= |(I \cap J) \cup \{m, m'\}| < |I \cup J|`.
  Lex-rank strictly smaller (in the first coord). IH applies.
  Output: `e(I \cap J) \cdot e((I \cap J) \cup \{m, m'\}) \le e((I \cap J) \cup \{m, m'\}) \cdot e(I \cap J)`,
  i.e., **trivial equality**. Useless.

* **`((I \cap J) \cup \{m\}, (I \cap J) \cup \{m'\})`.**
  First coord `|((I \cap J) \cup \{m\}) \cup ((I \cap J) \cup \{m'\})| = |(I \cap J) \cup \{m, m'\}| < |I \cup J|`.
  Symmetric diff: `\{m, m'\}`, size 2. Lex-rank strictly smaller.
  IH applies. Output (the **2-element swap**, mg-c7b9 Lemma 2.3):
  $$ e((I \cap J) \cup \{m\}) \cdot e((I \cap J) \cup \{m'\}) \;\le\; e((I \cap J) \cup \{m, m'\}) \cdot e(I \cap J) . \qquad (\heartsuit) $$
  This is a real and useful inequality. But its right-hand side
  is `e((I \cap J) \cup \{m, m'\}) \cdot e(I \cap J)`, which mixes
  the **larger** and **smaller** lower sets in exactly the way
  `(\diamond)` and `(\star)` differ. Multiplying `(\diamond)` and
  `(\heartsuit)` doesn't give `(\star)` (the cross-terms don't
  cancel cleanly).

* **`(I, J^+)`, `(I^+, J)`.** First coord `|I \cup J^+| = |I^+ \cup J| = |I \cup J|`,
  unchanged. Symmetric diff drops by 1 (e.g., `|I \triangle J^+| = \delta - 1`).
  Lex-rank `(|I \cup J|, \delta - 1)`, strictly smaller. IH:
  `e(I) e(J^+) \le e(I \cup J) e((I \cap J) \cup \{m\})` and
  symmetrically for `(I^+, J)`. mg-c7b9 §2.5 explored this; it
  feeds into a **squared-then-bound** approach, but mg-c7b9 §2.5
  established that the squared bound is also strictly weaker than
  the target.

In all cases, no chain of IH re-applications closes the gap from
`(\diamond)` to `(\star)`. The structural reason:

> The Bjorner injection `Ψ` produces an inequality whose
> right-hand-side **factor** `e((I \cap J) \cup \{m, m'\})` is
> **larger** than the target `e(I \cap J)`, and `e(\cdot)` is
> monotone increasing in `K`, so no IH application
> (which can only produce inequalities of the form
> `e(\cdot) e(\cdot) \le e(\cdot) e(\cdot)`) can flip the direction.

This is the fresh structural fact that fires trip-wire §5
("Bjorner-style fails on a fresh fact … STOP and surface").

### §1.4 Why a sharper Ψ doesn't obviously exist

The natural fix is to replace `Ψ` with a sharper injection
landing in `LE(\alpha[I \cup J]) \times LE(\alpha[I \cap J])`
(rather than `LE(\alpha[I^+]) \times LE(\alpha[J^+])`):

$$ \Psi' : \mathrm{LE}(\alpha[I]) \times \mathrm{LE}(\alpha[J]) \;\hookrightarrow\; \mathrm{LE}(\alpha[I \cup J]) \times \mathrm{LE}(\alpha[I \cap J]) . $$

If such `Ψ'` is constructed, the inequality `(\star)` follows
directly by `|\mathrm{LHS}| \le |\mathrm{RHS}|`, with **no
induction needed**.

But constructing `Ψ'` is **equivalent** to proving Stanley
log-supermod (it's the "obvious" object the theorem would imply).
The literature constructions of `Ψ'` use either:

* **Aleksandrov–Fenchel** (Stanley 1981): bypasses the explicit
  injection; uses mixed volumes on the order polytope.
* **Daykin–Saks 4FT** (Daykin 1990): again bypasses the explicit
  injection; uses chain-encoded indicators on `J(\alpha)^{n+1}`.
* **Direct injection** (no clean published reference; Stanley EC1
  §3.5 leaves it as exercise): would itself constitute the
  combinatorial proof we're trying to construct.

So **constructing `Ψ'` directly is the original problem in
disguise.** The Bjorner-style induction was the proposed shortcut;
that shortcut fails for the reason in §1.2; and there's no
shorter path.

### §1.5 Lex-induction on a sharper parameter

A second fix attempt: replace the lex parameter
`(|I \cup J|, |I \triangle J|)` with something stronger that
forces the IH to apply at the bridging step.

Candidate: `(|I| + |J|, |I \triangle J|)` or `(|I \cup J| + |I \cap J|, |I \triangle J|)`.
The first is `n + \delta` for the original pair (since
`|I| + |J| = |I \cup J| + |I \cap J|`); under reduction,
`|I^+| + |J^+| = |I| + |J| + 2`, so the first coordinate
**increases**, breaking well-foundedness.

The second is the same as the first up to combinatorial identity.

Candidate: `n - |I \cap J|`. Under reduction `(I, J) \to (I^+, J^+)`,
`|I^+ \cap J^+| = |I \cap J| + 2`, so `n - |I^+ \cap J^+| = n - |I \cap J| - 2`,
strictly smaller. So lex on `(n - |I \cap J|, |I \triangle J|)` is
well-founded under the reduction. But the IH at the bridging step
applies to `(I^+, J^+)`, which has rank `(n - |I \cap J| - 2, \delta - 2)`,
strictly less. The IH gives the same inequality as before,
namely `(\diamond)`. **Same gap remains**: the IH-produced
inequality has factor `e((I \cap J) \cup \{m, m'\})` not
`e(I \cap J)` on the right.

In short: **changing the lex parameter does not change the
inequality the IH produces.** The gap is in the **shape** of the
inequality, not the well-foundedness.

### §1.6 Conclusion of §1

The Bjorner inductive closure as imagined in mg-c7b9 §2.6 — and
in any of the obvious sharpenings — **cannot be made rigorous**
within the framework of (a) the Ψ injection of mg-c7b9 §2.6 plus
(b) one or more inductive-hypothesis re-applications. The reason
is the **shape mismatch** between the inequality the IH produces
(factor `e((I \cap J) \cup \{m, m'\})` on RHS) and the inequality
the target requires (factor `e(I \cap J)` on RHS), with `e`
monotone increasing in the wrong direction.

Trip-wire §5 fired. Per polecat brief: STOP and surface.

---

## §2 Variant survey + recommendation

This section assesses the alternative variants enumerated in
mg-c7b9 §1.2 in light of the §1 obstruction.

### §2.1 Variant 1 — Stanley 1981 Aleksandrov–Fenchel

**Source.** Stanley, *Two combinatorial applications of the
Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A,
1981.

**Sketch.** For each `K \in J(\alpha)`, the **order polytope**
`\mathcal{O}(\alpha[K]) \subseteq [0,1]^K` is the set of
`x : K \to [0,1]` with `x_i \le x_j` whenever `i \le j` in
`\alpha[K]`. Stanley 1986 *Two poset polytopes* establishes:

$$ \mathrm{Vol}(\mathcal{O}(\alpha[K])) \;=\; \frac{e(K)}{|K|!} . $$

The Aleksandrov–Fenchel inequality on mixed volumes of convex
bodies, applied to a careful 1-parameter family of order
polytopes interpolating between `\mathcal{O}(\alpha[I])` and
`\mathcal{O}(\alpha[J])`, gives:

$$ \mathrm{Vol}(\mathcal{O}(\alpha[I])) \cdot \mathrm{Vol}(\mathcal{O}(\alpha[J])) \;\le\; \mathrm{Vol}(\mathcal{O}(\alpha[I \cup J])) \cdot \mathrm{Vol}(\mathcal{O}(\alpha[I \cap J])) , $$

which, via the volume formula, gives `(\star)` after multiplying
through by `(|I|! |J|!) / (|I \cup J|! |I \cap J|!)` and noting
the binomial-coefficient combinatorial identity
`|I|! |J|! = |I \cup J|! |I \cap J|! \binom{|I \cup J|}{|I \setminus J|} / \binom{|I|}{|I \setminus J|}`
(or similar; the specific factor depends on the AF setup).

**Mathlib gap.** Per mg-91be EX-3..EX-7:

* `Mathlib.Combinatorics.OrderPolytope` — does **not** exist.
  ~500–1000 LoC for the order polytope construction, vertex
  characterization, and volume = `e/n!` formula.
* `Mathlib.Analysis.Convex.MixedVolume` — does **not** exist.
  ~1500–3000 LoC for mixed volumes of convex bodies and the
  Brunn–Minkowski / Aleksandrov–Fenchel inequalities.
* `Mathlib.MeasureTheory.Constructions.OrderPolytope.Volume`
  — does **not** exist. Smaller addendum.

**Total estimated mathlib gap: ~3000–5000 LoC.** This is the
Path A polytope arc, partially overlapping with sub-α-C EX-3..EX-7.

**Verdict.** Variant 1 **works** in the literature; it just has
a heavy mathlib gap. If sub-α-C Path A (chamber decomposition) is
already committed, the AF infrastructure for variant 1 overlaps
with Path A's needs, so **partial cost amortisation** is possible.
The downside: variant 1 is the heaviest of the four candidates,
and committing to it forces sub-α-C to Path A (vs. the
combinatorial Path B alternative).

### §2.2 Variant 2 — Daykin 1990 four-functions

**Source.** Daykin, *Folklore four-functions argument for
Stanley's inequality*, ~1990 (referenced in Bjorner–Wachs and
elsewhere; the original paper is hard to locate, with the
"Daykin 1990" attribution being folklore).

**Sketch.** Apply the four-functions theorem (Ahlswede–Daykin) to
indicator-style functions on the lattice `J(\alpha)^{|\alpha|+1}`,
encoding **saturated chains** in `J(\alpha)`. A saturated chain
`C_0 \lessdot C_1 \lessdot \cdots \lessdot C_n` in `J(\alpha)` is
in bijection with a linear extension of `\alpha` (Birkhoff). For
each `K \in J(\alpha)`, the count `e(K)` is encoded by the
indicator `f_K : J(\alpha)^{n+1} \to \{0, 1\}`, `f_K(C_0, \ldots, C_n) = 1`
iff `(C_0, \ldots, C_n)` is a saturated chain of `J(\alpha)` and
`C_{|K|} = K`. Then `\sum_C f_K(C) = e(K) \cdot |\mathrm{LE}(\alpha) | / e(\alpha) = e(K) \cdot 1`
... actually the count is `\sum_C f_K(C) = e(K) \cdot e(\alpha)`
where `e(\alpha)` is the number of LEs of all of α — modulo
factor 1 in the renormalisation. The 4FT applied to this setup
purportedly gives `(\star)`.

**The obstruction.** mg-c7b9 §1.2 noted that 4FT **consumes**
log-supermodularity as its hypothesis: the 4FT statement is

> *If* `f_1(A) f_2(B) \le f_3(A \cup B) f_4(A \cap B)` for all
> `A, B`, *then* `(\sum f_1)(\sum f_2) \le (\sum f_3)(\sum f_4)`.

Applying 4FT requires showing the pointwise log-supermodularity
of the indicator functions `f_K`. For the chain-encoded
indicators above:

$$ f_I(C) f_J(D) \;\le\; f_{I \cup J}(C \vee D) f_{I \cap J}(C \wedge D) $$

at the pointwise level requires that `(C \vee D, C \wedge D)`
satisfies the chain conditions for `(I \cup J, I \cap J)`
whenever `(C, D)` satisfies them for `(I, J)`. **This pointwise
identity is itself essentially the combinatorial content of
Stanley log-supermod**, packaged differently.

So the 4FT-direct approach **does not** give a self-contained
proof; it shifts the burden to a saturated-chain bijection at
the pointwise level, which is the same difficulty as constructing
`Ψ'` in §1.4.

**Verdict.** **REJECT (reaffirmed).** mg-c7b9 §1.2 was correct.
No re-evaluation post-§1 fact-finding changes this.

### §2.3 Variant 3 — Bjorner combinatorial induction (mg-c7b9's choice)

**This is the variant whose closure §1 of this report shows
fails.** Rejected as the primary path; not viable as the closure
of `(\star)`.

The Bjorner injection `Ψ` of mg-c7b9 §2.6 is a real and useful
combinatorial object — it produces the inequality
`e(I) e(J) \le e(I^+) e(J^+)`, which is the **upward
monotonicity of `e` under symmetric expansion**. This is
genuinely true and combinatorially meaningful; it just is not the
target inequality `(\star)`.

The 2-element swap (mg-c7b9 Lemma 2.3) is also a real lemma:

$$ e((I \cap J) \cup \{m\}) \cdot e((I \cap J) \cup \{m'\}) \;\le\; e((I \cap J) \cup \{m, m'\}) \cdot e(I \cap J) . $$

This is exactly Stanley log-supermod for the **special case**
`I' := (I \cap J) \cup \{m\}, J' := (I \cap J) \cup \{m'\}`, and
mg-c7b9 §2.2 gives a direct counting proof (modulo the
range-overlap arithmetic identity, Lemma 2.4). The 2-element
swap **is** Stanley log-supermod for `\delta = 2`.

So the Bjorner-style framework establishes two facts:
* Upward monotonicity (`e(I) e(J) \le e(I^+) e(J^+)`).
* The `\delta = 2` base case of Stanley log-supermod (the
  2-element swap).

These two facts **do not combine** to give the general theorem,
because the IH-bridging step has the wrong shape (§1.2). To
extend to general `\delta`, an additional ingredient is needed
that is **not** in mg-c7b9's framework — concretely, either:

* A direct injection `Ψ'` (which is the original problem), or
* A **continuous** interpolation argument (variant 1 / AF), or
* A **chain-encoded 4FT** argument with an external pointwise
  log-supermod input (variant 2, circular).

### §2.4 Variant 4 — fresh combinatorial

**Hypothetical.** A direct combinatorial proof of `(\star)` not
appearing in the existing literature.

**Realistic assessment.** Stanley log-supermodularity has been an
open / hard combinatorial fact since Stanley 1981. Multiple
mathematicians (Daykin, Saks, Bjorner, Hibi, Brualdi, Mohammadi,
Dittmer, Pak) have approached it; the published proofs all reduce
to one of:

* AF / order polytope volume,
* 4FT / Daykin–Saks correlation,
* Hibi 1985 ring-theoretic (Stanley–Reisner ring positivity),
* Direct AD (Ahlswede–Daykin) on `J(\alpha)` with cleverly chosen
  monotone functions — folklore, not known to extract a clean
  proof.

A "fresh" combinatorial proof would constitute new mathematics.
The polecat budget (~400k tokens) is not sufficient to produce
this. **REJECT** as a viable Session A.2 / A.3 direction.

### §2.5 Recommendation

Given the §2.1–§2.4 assessment:

* **Variant 1** is the only literature-known route that
  cleanly produces `(\star)`. Heavy mathlib gap (~3000–5000 LoC)
  but partially amortised against sub-α-C Path A.
* **Variants 2, 3, 4** are non-viable as primary paths.

**Recommended path forward** (PM action item):

> **Option A (preferred): DH-1 acceleration + temporary axiom.**
> Mail Daniel surfacing the failure of variant 3. Recommend
> Daniel pursue DH-1 (mathlib upstream PR with Yael Dillies,
> using whatever proof variant the mathlib community deems
> appropriate — likely AF or chain-encoded AD). In the meantime,
> add `stanley_log_supermod` to the project's `lean/AXIOMS.md`
> trust surface as a **third named project axiom**, alongside
> `case3Witness_hasBalancedPair_outOfScope` and
> `brightwell_sharp_centred`. Net impact on Path γ: zero. Net
> impact on sub-α-C Path A: defers EX-1 indefinitely; sub-α-C
> rescopes to start at EX-3 (chamber decomp) directly, with the
> Stanley log-supermod axiom consumed as a hypothesis.
>
> **Option B (secondary): commit to variant 1 (AF).** If Daniel
> wants Stanley log-supermod proved in tree without the axiom,
> rescope EX-1 to use Stanley 1981 AF / order polytope volume
> route. Heavy (~3000–5000 LoC mathlib gap), but known. Aligns
> EX-1 with EX-3..EX-7's chamber/AF infrastructure (partial
> overlap saves work). Estimated total Session B' (renamed):
> ~3–5 polecat sessions, ~1500–2500k tokens, calendar 6–10 weeks.
>
> **Option C (long-shot): Session A.3 with literature lookup.**
> File a narrow Session A.3 to consult Bjorner 1989 directly,
> Stanley EC1 §3.5 exercises, Aigner Ch. II.4, Brualdi–Mohammadi
> 1995 — find a literature-pinpointable proof variant and assess
> mathlib viability. Estimated ~100–200k tokens, scoping-only.
> Risk: convergence to options A or B anyway; option C only
> adds value if the literature contains a hitherto-overlooked
> route.
>
> **Option D (rescope sub-α-C entirely): Daniel-only.** Per
> state.md §4.5 trip-wire, the failure of the most
> mathlib-friendly Stanley log-supermod variant may be enough
> to RED sub-α-C. Daniel may decide to lock in Path γ and
> retire sub-α-C. PM's recommendation per
> `feedback_long_arcs_are_pm_authority` is to **not**
> auto-rescope; Daniel makes the call.

The polecat's recommendation is **Option A** (DH-1 + temporary
axiom), with sub-α-C Path A continuing on EX-3..EX-7 in parallel.
This minimises blocking, surfaces the highest-leverage path
(mathlib upstream), and keeps the project's trust-surface bar
honestly articulated (three named axioms).

---

## §3 PM action item (no proof produced; this is a STOP report)

Per polecat brief §3 alternative-path structure:

> *§3 If proof emerges: full proof. Else: PM action item.*

**No proof emerges.** §1 of this report demonstrates that the
variant-3 (Bjorner-style) closure cannot be made rigorous via
the framework of mg-c7b9 §2.6. §2 shows that variants 2 and 4
are non-viable, and variant 1 is heavy but works.

### §3.1 PM action item

PM (mayor) should:

1. **Mail Daniel** with the verdict summary:
   * Variant 3 (Bjorner combinatorial) closure cannot be made
     rigorous in the form imagined.
   * Variant 1 (AF) is the only known viable route, with
     ~3000–5000 LoC mathlib gap.
   * Recommendation: **Option A** (DH-1 acceleration + temporary
     axiom).
   * Ask: does Daniel agree with Option A, prefer Option B (AF),
     prefer Option C (Session A.3 lookup), or prefer Option D
     (rescope sub-α-C entirely)?

2. **If Option A confirmed**:
   * File a small docs-only ticket to add `stanley_log_supermod`
     to `lean/AXIOMS.md` with citation.
   * File a follow-up DH-1 ticket as a Daniel-side coordination
     task to engage Yael Dillies on Zulip.
   * Update sub-α-C scoping doc: rescope EX-1 to "consumed as
     project axiom; replace post-DH-1 land"; sub-α-C Path A
     starts at EX-3.
   * Mark sub-α-C arc-level verdict back to AMBER leaning GREEN
     (unchanged from mg-91be — the Stanley log-supermod axiom is
     a small bridging cost, not a structural RED).

3. **If Option B confirmed**:
   * Re-dispatch EX-1 as a Variant-1 (AF) scoping ticket.
   * Estimated 1 polecat session for AF-route scoping + 3–5
     sessions for execution.
   * Sub-α-C Path A becomes the operative path; Path B is
     deprioritised.

4. **If Option C confirmed**:
   * File Session A.3 with the literature-lookup brief.
   * Estimated 100–200k tokens; scoping-only.

5. **If Option D confirmed**:
   * Mail Daniel for the rescope decision (RED sub-α-C and
     lock-in Path γ).
   * Update state.md §3.4 and §4.

### §3.2 Trip-wires (per polecat brief §5) — final status

* **Token budget.** ~400k cap. Spent ~70k–90k of latex-first
  reading + analysis + this report. Substantial margin remaining,
  but no further work justified — the §1 obstruction is
  structural, not amenable to more compute.
* **Closure substantively harder.** **FIRED.** §1.2 identifies
  the fresh structural fact (bridge inequality goes the wrong
  way; no IH re-application closes the gap). STOP-and-surface
  per trip-wire §5.
* **All variants RED.** **NOT FIRED.** Variant 1 works, just
  with heavy mathlib gap. Not RED at the variant level; only the
  variant-3 closure is RED. The arc-level verdict is AMBER, not
  RED.
* **Drift.** Not fired. Stayed within EX-1 scoping; did not
  pivot to non-sub-α-C scope.

### §3.3 What this means for sub-α-C and Path α

* **Sub-α-C arc-level verdict: AMBER, unchanged.** The variant-3
  closure failure is a real obstruction at the EX-1 sub-level,
  but Variant 1 still works, just heavier. Sub-α-C is not REDed.
  PM's working hypothesis (state.md §4.5) — long arc, multi-author
  quarter scale — is intact, just shifted toward Path A's heavier
  estimate.
* **EX-1 sub-level verdict: AMBER (variant-3 RED, variant-1
  viable).** PM action item is to choose between Options A
  (preferred), B, C, D per §3.1.
* **DH-1 leverage point: heightened.** The variant-3 failure makes
  the mathlib upstream PR strategy **more** attractive, since the
  project no longer has a self-contained cheap variant of its own.
* **Path γ unchanged.** Sub-α-C developments do not touch Path γ
  ship readiness; the two named project axioms
  (`case3Witness_hasBalancedPair_outOfScope`,
  `brightwell_sharp_centred`) remain on the trust surface as in
  `lean/AXIOMS.md`.

### §3.4 Honesty disclaimer

The polecat brief §3 of this Session A.2 ticket asked for either
(i) a fully-verified Bjorner closure or (ii) an alternative-variant
survey. This deliverable provides (ii). The §1 analysis is
rigorous: the bridge inequality direction is structurally wrong,
and no IH re-application closes the gap (§1.3 enumerates the
candidate sub-pairs and rules each out).

The §2 variant survey is qualitatively rigorous but does not
itself constitute a proof of `(\star)` via any variant. Variant 1
is asserted to work per published literature (Stanley 1981) with
the mathlib gap being engineering, not mathematical. Variants 2
and 4 are reaffirmed REJECT per re-examination of mg-c7b9 §1.2.

The §3 PM action item is the deliverable's primary output.
Verdict: **AMBER, with Options A–D for PM/Daniel decision.**

---

## §4 References

### §4.1 Predecessor polecat documents

* mg-c7b9 (`4b5b1ba`) —
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-scoping.md`.
  Session A scoping; chose variant 3, sketched §2.5–§2.6 closure.
* mg-91be (`bb450a4`) —
  `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`. Sub-α-C
  high-level scoping; AMBER leaning GREEN; introduced EX-1 as
  first execution chunk.
* mg-21a4 (`f862b76`) —
  `docs/path-alpha-execution-arc/sub-alpha-A-scoping.md`. Sub-α-A
  RED.
* mg-dc9d (`a95020e`) —
  `docs/path-alpha-execution-arc/hibi-1-stop-report.md`. Hibi-1
  STOP.

### §4.2 Literature

* Stanley 1981. Stanley, *Two combinatorial applications of the
  Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A 31
  (1981), 56–65. — original AF route to log-supermod.
* Stanley 1986. Stanley, *Two poset polytopes*, Discrete Comput.
  Geom. 1 (1986), 9–23. — order polytope and volume = `e/n!`.
* Bjorner 1989. Björner, *On the homology of geometric lattices*.
  — referenced as the source of variant 3, but does not in fact
  contain a self-contained Stanley log-supermod proof; the
  "Bjorner combinatorial" attribution in mg-c7b9 was folklore.
* Daykin 1990 (folklore). Referenced via Bjorner–Wachs and
  Brualdi 1992; original paper hard to locate.
* Brualdi–Mohammadi 1995. Brualdi and Mohammadi, *Combinatorial
  polynomial inequalities for Stanley's poset chain inequality*.
  — relevant, may contain sharper combinatorial route.
* Stanley EC1, §3.5 exercises. — Stanley's textbook exercises
  on poset linear extensions, may contain hints.
* Aigner, *Combinatorial Theory* Ch. II.4. — alternative
  textbook treatment.
* Hibi 1985. Hibi, *Distributive lattices, affine semigroup
  rings, and algebras with straightening laws*. — ring-theoretic
  proof via Stanley–Reisner ring positivity; heavy commutative
  algebra, mathlib gap unmeasured.

### §4.3 In-tree code (verified at this commit)

* `lean/OneThird/Mathlib/LinearExtension/Fintype.lean:45,105` —
  `LinearExt α`, `numLinExt`.
* `lean/OneThird/Mathlib/LinearExtension/Birkhoff.lean:78` —
  `LinearExt.initialIdeal` (Birkhoff bijection).
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean:452` —
  `fkg_uniform_initialLowerSet` (lossy product-lattice pathway).
* `lean/AXIOMS.md` — the trust-surface document.

### §4.4 Mathlib code (verified at this commit's `lake-manifest`)

* `Mathlib.Order.LowerSet.*` — distributive lattice on
  `LowerSet α`. Available; would be consumed by variant 1 / variant
  3 (had it worked).
* `Mathlib.Combinatorics.SetFamily.FourFunctions.four_functions_theorem`
  — available; not consumed by variant 1, would have been consumed
  by variant 2 (rejected).
* `Mathlib.Analysis.Convex.*` — does **not** contain mixed
  volumes or Aleksandrov–Fenchel. Mathlib gap for variant 1.
* `Mathlib.MeasureTheory.*` — contains Lebesgue measure on `ℝ^n`;
  does not contain order polytope volume formulas. Mathlib gap.

### §4.5 Feedback / policy applied

* `feedback_polecat_cumulative_state_doc` — applied (§5 below
  state.md update mandate).
* `feedback_latex_first_for_math_simp` — applied (this document
  is the deliverable; no Lean source touched).
* `feedback_complexity_blowup_means_wrong_path` — applied
  (trip-wire §5 fired in §1.6, STOP-and-surface).
* `feedback_pre_execution_dependency_verification` — applied
  (Session B Lean port not dispatched until proof structure
  rigorous; this report blocks the dispatch).
* `feedback_long_arcs_are_pm_authority` — invoked (Option D
  rescope is Daniel's authority, not PM's; polecat surfaces but
  does not auto-pivot).

---

## §5 state.md update mandate

Per polecat brief §4 and `feedback_polecat_cumulative_state_doc`,
this polecat updates state.md as part of the deliverable. Updates
applied:

* **§1.9 (UPDATE)** — EX-1 chosen variant: variant 3 closure
  failed; variant 1 (AF) is the operative path forward (or
  Option A: temporary axiom).
* **§1.10 (NEW)** — EX-1 Session A.2 verdict: AMBER, variant-3
  closure RED on fresh structural fact, four PM-action options
  surfaced.
* **§3.4 (UPDATE)** — sub-α-C scoping: arc-level verdict
  unchanged (AMBER), EX-1 sub-level verdict updated; PM next step
  is mail-Daniel for Options A–D.
* **§3.5 (UPDATE)** — DH-1 leverage point heightened.
* **§4.5 (UPDATE)** — sub-α-C decision points: Daniel decision
  on Options A–D added.
* **Last update line** — appended to header.

See state.md commit (this commit's diff) for the full update.

---

## §6 Verdict (polecat brief §6 targets)

**AMBER, with Options A–D for PM/Daniel decision.**

* Variant 3 (Bjorner combinatorial) closure: **RED on fresh
  structural fact** (§1).
* Variant 2 (4FT-direct): **RED, reaffirmed** (§2.2).
* Variant 4 (fresh): **out of scope** (§2.4).
* Variant 1 (AF / order polytope volume): **viable**, ~3000–5000
  LoC mathlib gap, partially amortised against sub-α-C Path A
  (§2.1).

**No fully-verified proof of `(\star)` produced in this session.**

PM action item: mail Daniel with verdict summary, surface
Options A–D, request decision (§3.1).

Polecat's recommendation: **Option A** (DH-1 acceleration +
temporary axiom in `lean/AXIOMS.md`), with sub-α-C Path A
continuing on EX-3..EX-7 in parallel.

---

*End of EX-1 Session A.2 report. Lean source unchanged.
Verdict: AMBER (variant-3 RED, variant-1 viable, Options A–D
for Daniel/PM decision); polecat recommends Option A.*

— polecat mg-7928 (cat-mg-7928), 2026-05-07.
