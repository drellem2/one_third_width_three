# mg-e768's three unfiled follow-ups, settled (mg-65f5)

*Successor to mg-e768; carries its R1, R2, R3. R4 was delivered by ae768 and is not re-done here.*

**Scope note on repositories, stated first because it constrains what this commit can contain.**
R1's edit target is `onethird_program/STATE.md`; R2's is `onethird_program/STATE.md`'s ledger row 6.
This work item's refinery target is `one_third_width_three`. **The two are different repositories.**
Everything I could *verify* lives here (`step8.tex`, `docs/probe-lambda-constant-bound.md`,
`docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md`, `docs/OneThird-CounterexampleSearch-C.md`);
everything I would *edit* lives there. So this document carries the findings and the exact patch
text, and the patch is mailed to mayor and pm-onethird rather than applied. **No `STATE.md` line was
touched by this ticket.**

---

## 0. Verdict in four lines

1. **R1 is SETTLED, and neither of the ticket's two readings is right.** It is not a false belief and
   not a name/gloss slip. **Standard dominance is L1b's *conclusion*, not its input** — listing it as
   machinery L1b stands on is a **circularity**, and it is why two workers could not settle a fork
   that presupposed 3b was an input. §1.
2. **R2 is SUPERSEDED — and the requested repair must NOT be performed.** mg-957a (commit `d41d18c`)
   already settled F12 by reading the source, and settled it *the other way*: the width-3 hypothesis
   is **present and inert**. I re-verified that independently, from `step8.tex` in this repo, all
   four proofs. **Repairing the cell to width-3 would introduce an error.** §2.
3. **R3/Q2 is YES, and it is FREE.** A minimal counterexample has width ≥ 3 — from **Linial 1984**,
   which has **no exception class**. ae768's caveat ("depends on Sah's width-2 exception class") is
   **misplaced**: Sah is the *strengthening* to δ ≥ 0.33876 and is the thing that carries an
   exception class; the reduction needs only δ ≥ 1/3 at width 2. It holds via Sah too. §3.
4. **R3/Q1 is NO** — the consecutive-antichain lemma is not in the corpus, within the search scope
   declared at §4.1. Its four-line proof is **correct**; I checked it. §4.

A fifth thing I was not asked for and found on the way: **row 3b's `0/132` is a sampling artifact,
not a clean sweep** — 166 explicit refuters exist outside the population that produced it. §1.4.

---

## 1. R1 — what L1b's reduction consumes

### 1.1 The question, verbatim

> DOES L1b'S REDUCTION CONSUME ROW 3a ALONE, OR DOES IT NEED ROW 3b?

with the ticket's fork attached: 3a alone ⟹ the old *"all proven"* was a **NAME/GLOSS SLIP**; 3b
needed ⟹ it was a **FALSE BELIEF**.

**The answer is neither, because the fork is malformed.** It presupposes that row 3b is an *input* to
L1b's reduction. It is not. It is that reduction's *output*.

### 1.2 The settling observation, and it is a definition rather than a theorem

`λ_std` is **not** an eigenvalue of the BK graph. Both live definitions agree:

- `STATE.md` glossary: *"top eigenvalue of the symmetrized transport operator on `1⊥`"*;
- [`docs/probe-lambda-constant-bound.md:65`](probe-lambda-constant-bound.md) (this repo), explicitly:

```
T[x,i] = Pr[ sigma(x) = i ],     S = (T + T^T)/2,     lambda_std = max spec( S |_{1-perp} ).
```

That is an **`n × n` matrix over the elements of `P`**, not a matrix over `L(P)`. Nothing about
"which block of the BK spectrum carries `λ₂`" is needed to *define* it, and — the point — nothing
about it is needed to *bound* it either.

### 1.3 What the reduction actually consumes: rows 5 and 7, and nothing else

mg-210d's master bound is the object `STATE.md` itself already names as the one *"every sufficient
condition in row 8 lands on"*. Its proof chain, re-read line by line in this repo:

| step | content | what it spends |
|---|---|---|
| Lemma 1.1 (Buser tool) | `1 − λ_std ≤ n·leak(A)/(\|A\|\|Aᶜ\|)` | Rayleigh quotient on `S\|_{1⊥}` with `f = 1_A − a·1`; `T` doubly stochastic; `S1 = 1`. **Row 5.** |
| Lemma 2.1 | `Σ_k leak_k = E[F]/2` | a counting identity |
| Lemma 2.2 | `E[F] ≤ 2E[inv]` | Diaconis–Graham upper half, re-derived from scratch. **Row 7.** |
| Lemma 2.3 | `Σ k(n−k)/n = (n²−1)/6` | arithmetic |
| **Thm 2.4** | **`1 − λ_std ≤ 3E[F]/(n²−1) ≤ 6E[inv]/(n²−1)`** | the mediant inequality |

**No sector decomposition, no representation theory, and no claim about which irrep carries `λ₂`
appears anywhere in it.** The chain `frozen ⟹ LIB ⟹ (LIB-weak) ⟹ λ_std → 1` runs entirely inside the
transport matrix. Row 3b is never invoked.

This is not a new reading: `STATE.md`'s own (A)-SPREAD strike paragraph already says the master bound
is *"Buser-over-prefix-cuts plus a mediant relaxation, **unconditional**, consuming rows 5 and 7"*.
**That sentence already answers R1 and nobody noticed, because it was written to settle a different
bullet.**

And the gloss's operative clause — *"so a combinatorial bound controls `λ_std`"* — **is Theorem 2.4
itself**: `E[inv]` is the combinatorial bound, `λ_std` is what it controls. Proven, unconditional,
any width, `U`/`U-id` throughout.

> **This is where I differ from ae768, and I am contradicting its stated view.** It argued the
> operative clause *"needs the standard block to carry the second eigenvalue, which is row 3b"*.
> That would be right if `λ_std` meant *"`λ₂^BK`, restricted to the standard block"*. It does not
> mean that — it is defined directly as `max spec(S|_{1⊥})`, and Theorem 2.4 bounds that object
> directly. ae768 flagged its own view as unasserted and named the settling question; the settling
> question has an answer and it goes the other way.

### 1.4 Where standard dominance actually sits: it is L1b

[`docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md`](OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md)
§5 — L1b's own document, in this repo — states it outright:

> **`L1b ⟺ "all-pairs-frozen ⇒ standard dominance"`**, and LIB (§4) is its quantitative form.

with the mechanism spelled out at `:288`:

> `1 − λ₂^BK ≤ 2/(γn)` is rigorous (Theorem E) — **but `λ_std ≤ λ₂^BK`** (the standard sector is a
> subspace): Theorem E bounds the gap **in the wrong direction** for the transport quotient. The
> transfer needs the slow mode to have a real standard-sector component — **standard dominance**.

So on the Cheeger route, standard dominance is **exactly the missing implication** — i.e. the wall,
i.e. row 8. Listing it at `:76` as *machinery L1b's reduction stands on* records **the open problem as
its own premise**. That is a third failure mode, and a worse one than either fork: a false belief is
wrong about a dependency, a gloss slip is wrong about a label, but this one **makes the open problem
look discharged by listing it under its own feet**.

### 1.5 A live defect in row 3b's own warrant, found while checking the above

Row 3b is ledgered `FP`, *"empirical (0/132)"*, and mg-957a's prose contrasts it with row 10 as
*"a clean sweep like row 3b's `0/132`"*. **It is not a clean sweep.** Two sources in this repo:

- [`OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md:286`](OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md)
  gives the `0/132` and states its own frame: **`n ≤ 6` exhaustive + `n = 7` top-λ spot-check**.
- [`OneThird-L1b-BK-Transport-Transfer-Probe.md`](OneThird-L1b-BK-Transport-Transfer-Probe.md) (mg-8b64)
  finds **166 explicit refuters** at moderate-λ `n = 7` — *outside* that spot-check. L1b's own doc at
  `:311` says so in as many words: the kill-shot *"reported standard dominance universal, but only
  checked `n ≤ 6` exhaustively and `n = 7` at the highest-λ posets; the moderate-λ `n = 7` refuters,
  outside that spot-check, violate it."*

**So `0/132` is `0` failures in a frame chosen so that the known failures are not in it.** Standard
dominance **as an unconditional statement is refuted**, not unproven; only its *conditional*
(all-pairs-frozen) form is open — and that conditional form is L1b. Row 3b's `FP` mark, and the
`0/132` beside it, both overstate what is there.

### 1.6 The repair (patch text — NOT applied; different repository)

**`onethird_program/STATE.md:76`** — strike the bullet, as `:78`'s (A) SPREAD bullet was struck, and
for a strictly stronger reason:

```markdown
- ~~**standard dominance** (gap lives in the standard sector, so a combinatorial bound controls
  `λ_std`) — `FP`, row 3b.~~ **STRUCK — IT IS L1b'S CONCLUSION, NOT ITS INPUT (mg-65f5).** Listing
  it here recorded the open problem as its own premise. `λ_std` is *defined* as
  `max spec(S_P|_{1⊥})` (glossary; `probe-lambda-constant-bound.md:65`), an `n × n` transport
  object — not a block of the BK spectrum — so no dominance statement is needed to bound it. The
  operative clause *"a combinatorial bound controls `λ_std`"* **is mg-210d's master bound**
  `1 − λ_std ≤ 6E[inv]/(n²−1)` (Thm 2.4), whose whole proof spends **row 5** (Buser test vector on
  `S|_{1⊥}`) and **row 7** (Diaconis–Graham) and nothing else — as this document's own (A) SPREAD
  paragraph already says. On the Cheeger route standard dominance is the *missing* transfer
  (`λ_std ≤ λ₂^BK`, so Theorem E bounds the gap in the wrong direction —
  `OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:288`), i.e. **`L1b ⟺ all-pairs-frozen ⇒ standard
  dominance`** (ibid. `:310`). It stays on the board as **row 8**, where it already is.
```

**`STATE.md:81`** — the UNRESOLVED paragraph is discharged; replace with:

```markdown
**RESOLVED (mg-65f5) — AND THE FORK WAS MALFORMED.** The question *"does L1b's reduction consume row
3a alone or need row 3b?"* presupposed 3b is an input. It is not: it is L1b's conclusion (see the
struck bullet). The reduction consumes **rows 5 and 7**. Row **3a** (`S_P = ρ_std(η_P)`, `U-id`) is
the dictionary that licenses the word *"standard"* for `S_P`; Theorem 2.4 bounds `S_P|_{1⊥}`
directly and does not invoke it as a lemma. So the old *"all proven"* was neither a **FALSE BELIEF**
about a dependency nor a **NAME/GLOSS SLIP** about a label — it was a **CIRCULARITY**, and it is the
reason two workers could not settle the fork as posed.
```

**Consequence for the machinery set's weakest kind, flagged because it moves a ⚠️ headline.** After
this strike the set at `:74` is {row 5 `U`, row 7 `U-id`} and its weakest kind is **`U`**, not `FP`.
That does **not** re-license the sentence mg-957a corrected. That sentence was false because it
called a set all-proven *while the set contained an `FP` member*; the finding here is that the `FP`
member was never a member. **Whoever lands this must re-derive the `:74` warning rather than delete
it**, and must not let "weakest kind is now `U`" be read as "L1b's machinery is proven" — L1b itself
is open, and it is open *as* standard dominance.

**Coordination.** mg-5827 landed at `bb8d206` and struck the (A) SPREAD bullet at this same site. I
read that landing before writing the above; this patch strikes a **different bullet** in the same
list and reuses mg-5827's strike format deliberately. It does not touch `:78`.

---

## 2. R2 — ledger row 6's Width cell: superseded, and the requested repair is now wrong

**Do not repair the cell to width-3.** The ticket's instruction was written against a ledger state
that no longer exists.

mg-957a (`d41d18c`, `onethird_program`) settled F12 by reading `step8.tex` and found the width-3
hypothesis **present but never consumed**, so `any` is the correct entry and the cell now carries its
derivation. The ticket's bound — *ae768 established only that the hypothesis is PRESENT, not that it
is ESSENTIAL* — is exactly right, and mg-957a closed precisely that gap.

**I verified it independently, from `step8.tex` in this repo, and it holds.**

**Site census — mg-957a says 5 sites; confirmed exactly.** `grep` for width-3 in `step8.tex` returns
`:21` (blanket Setup), `:60`, `:158`, `:196`, `:332` in §G1, and then `:424` onward — all of which are
in the **downstream cascade** (§G2+), which mg-957a explicitly excluded and which is genuinely
width-3. No §G1 site is missed.

**Consumption — all four proofs read, and the hypothesis is inert in each:**

| proof | lines | what it spends | width-3? |
|---|---|---|---|
| `lem:dirichlet-conductance` | 122–152 | `π(S)π(Sᶜ) ≤ min(π(S),π(Sᶜ))` and the definitions of `Q`, `vol`, `Φ`. A general reversible-chain inequality; no poset structure enters at all | **no** |
| `lem:indec-incompairs` | 167–195 | indecomposability only, via an ordinal-sum split `(A∪{x}) ⊕ B`. The statement does not even mention width | **no** |
| `lem:frozen-pair-existence` | 196–270 | Step 1: ≤ `n−1` adjacent positions per `σ`. Step 2: the `γ`-counterexample hypothesis. Step 3: `I(P) ≥ n/2` from the previous lemma. Step 4: min ≤ ratio-of-sums | **no** |
| Thm `cex-implies-low-expansion` | 330–370 | the two lemmas, plus `p_xy ≥ γ` from the counterexample hypothesis | **no** |

Delete `width-3` from `:60` and the same four proofs stand verbatim. **mg-957a's finding is
CONFIRMED, and R2 needs no edit.**

**What I did not check, because mg-957a did not either and it is the part that could still bite:**
the Lean artifact (`lean/OneThird/MainTheorem.lean`) may carry `width-3` as a formal hypothesis, and
this is a reading of the LaTeX, not a machine check.

---

## 3. R3 / Q2 — a minimal counterexample has width ≥ 3: **YES**, and Sah is not needed

**ae768's caveat is misplaced.** It attached the reduction to Sah's exception class:

> Q2 depends on Sah's width-2 exception class, WHICH IT DID NOT READ.

The reduction does not depend on it. The reduction needs `δ ≥ 1/3` at width 2. That is **Linial 1984**
("The information-theoretic bound is good for merging"), which proves the **1/3–2/3 conjecture itself**
for width-2 posets and has **no exception class**. Sah is the *strengthening* to `δ ≥ 0.33876`, and
the exception class is a feature of the *gap*, not of the conjecture. ae768 read `STATE.md:204`
(*"The gap above 1/3 is proven for width-2 (Sah…)"*) — a sentence about the gap — and inherited its
qualifier onto a claim that does not carry it.

**Proposition (Q2).** Every counterexample to 1/3–2/3 has width ≥ 3; in particular a minimal one does.

*Proof.* Let `P` be a finite non-chain poset with `δ(P) < 1/3`, and suppose `width(P) ≤ 2`. `P` is a
non-chain, so `width(P) = 2`, and Linial 1984 gives `δ(P) ≥ 1/3` — contradiction. ∎

**It also holds via Sah, so the answer is robust to the routing.** I read Sah's statement at the
source (arXiv:1811.01500 abstract): width-2 posets *not* constructible from the singleton and the
three-element one-relation poset `E` by direct sum satisfy `δ ≥ (−3+5√17)/52 ≈ 0.33876`. Take
`width(P) = 2` with `δ(P) < 1/3`:

- **`P` outside the exception class.** `δ(P) ≥ 0.33876 > 1/3`. Contradiction.
- **`P` inside it**, `P = Q₁ ⊕ ⋯ ⊕ Q_k` with each `Q_i ∈ {1, E}`. Incomparable pairs of an ordinal
  sum lie inside one summand and their order probabilities are computed there (the ordinal-sum
  marginal identity — the corpus's one exact restriction law), so `δ(P) = max_i δ(Q_i)` over
  non-chain summands. If some `Q_i = E` then `δ(P) = δ(E) = 1/3`, contradicting `δ(P) < 1/3`. If
  every `Q_i = 1` then `P` is a chain, excluded. ∎

**The exception class never obstructs the reduction, and the reason is worth stating plainly: its
members sit *at* `1/3`, not below it.** The conjecture is `δ ≥ 1/3`, non-strict, so equality is
compliance. That is the fact ae768 could not check and it is what makes Q2 free.

`δ(E) = 1/3` verified here by hand, not taken from the corpus: `E = ({a,b,c}, a<b)` has the three
linear extensions `cab, acb, abc`; `Pr[c<a] = 1/3` and `Pr[b<c] = 1/3`, so
`δ(E) = max(1/3, 1/3) = 1/3`. (The corpus's five-engine check agrees —
[`OneThird-CounterexampleSearch-C.md`](OneThird-CounterexampleSearch-C.md) §3.2.)

**"Direct sum" is unambiguous here.** Sah's theorem is about **width-2** posets, and only the
*ordinal* sum keeps width at 2 — a disjoint union of two width-2 pieces has width up to 4. So the
closure is the ordinal-sum one, which is also how the corpus reads it
(`OneThird-EntropyDiscontinuity-Mechanism.md:453`).

### 3.1 Already known, and already unledgered — which is the actionable half

The width-≥3 conclusion is **already in the corpus**, landed hours before this ticket:
`onethird_program/docs/OneThird-Literature-LowerBound-MinimalCounterexample-mg-33f5.md:101,119`
tabulates *"width two | Linial 1984"* among the proved classes and concludes a
minimal counterexample must be *"rigid, of **width ≥ 3**, not N-free…"* — adding, at `:262`, that
**nothing in the corpus records it**.

That is still true of `STATE.md`. **The deliverable for Q2 is therefore not a proof — it is a ledger
row**, which is what makes it the reduction *"several arguments would want"*. Suggested entry
(again, not applied — different repository):

```markdown
| 12 | **minimal counterexample ⟹ width ≥ 3.** Linial 1984 proves 1/3–2/3 for width-2 posets,
with **no exception class**; a non-chain of width ≤ 2 has width exactly 2. (Sah arXiv:1811.01500
gives the same reduction independently: its exception class — ordinal sums of `1` and `E` — has
`δ = 1/3` **exactly**, which complies with the conjecture. Sah's `δ ≥ 0.33876` is the *gap*
strengthening; the exception class is a feature of the gap, not of the reduction.) | `U` |
**proven (literature)** | forces width ≥ 3 |
```

**Bound words, since that is this ticket's subject.** This row is `U` **by citation**, not by
anything derived in this corpus: I did not verify Linial 1984 or Sah, and read Sah's statement only
at the abstract. The reduction *from* those results is elementary and is written out above.

---

## 4. R3 / Q1 — is the consecutive-antichain lemma already in the corpus? **NO**

ae768's Q1 asks whether its four-line lemma — *G‴'s hypothesis is satisfied by every finite poset of
width ≥ 3* — is already somewhere in the corpus. **I swept and did not find it.**

**The lemma is correct.** I checked the four lines rather than assuming them. For a 3-antichain
`A = {a,b,c}` put `L = {d ∉ A : d < some a ∈ A}`:

- `L ∩ U = ∅` — `d` in both gives `a' < d < a`; `a ≠ a'` contradicts the antichain and `a = a'`
  contradicts strictness. ✓
- `L` and `L ∪ A` are down-sets — `e < d < a` puts `e ∈ L` unless `e ∈ A`, and `e ∈ A` with `e < a`
  contradicts the antichain. ✓
- **no `a ∈ A` lies below any `d ∈ L`** — `a < d < a''` forces `a < a''`, contradiction. (ae768 does
  not state this step; it is what makes the concatenation a linear extension, and it holds.) ✓

so `(lin ext of L)(A in any order)(lin ext of the rest)` is a linear extension of `P` whose prefix
ideals form a compatible ordered partition with one block `A` and singletons otherwise — which is
G‴'s hypothesis verbatim (`OneThird-Hodge-Side-Leverage.md`, row **G‴**: *"one antichain of size ≥ 3
and singletons otherwise"*). Width ≥ 3 supplies the 3-antichain.

**Corroborating circumstantial evidence that it is genuinely absent:** row G‴'s own cell says
*"Nothing here consumes it either"*. Had the lemma been on the board, G‴ would immediately have
yielded a pointwise-universal at unbounded n, and that is not a consequence anyone would leave
unrecorded.

**What this does and does not buy — ae768's own scope note, which I am not weakening.** It is **one**
level, hence one factor of `≤ 1/2` in `Π(1 − γ_i)`. It is **not** the `2^{Θ(n)}` loss, and row **J**
(joins suppress `λ₂`) blocks the obvious extension to lower levels. I did **not** verify the
`γ_i ≥ 1/2` consequence — that is G‴ + Theorem L, which I did not re-derive.

---

## 4.1 Coverage — what I checked, what I did not, and what each verdict rests on

Matching ae768's practice of naming the frame rather than implying completeness.

**Checked, by reading the source in this repo:** `step8.tex` §G1 in full (4 proofs, lines 15–375);
`probe-lambda-constant-bound.md` §§1–2 (master bound and all four lemmas);
`OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md` §5; `OneThird-CounterexampleSearch-C.md` §0–§1;
`OneThird-Hodge-Side-Leverage.md` row G‴. **Read at the source outside the corpus:** Sah
arXiv:1811.01500 (abstract only), Linial 1984 (secondary, via the 1/3–2/3 survey).

**Not done:**

- **I did not verify Linial 1984 or Sah's Theorem 1.4.** Q2's row is `U`-by-citation. I read Sah's
  abstract, not its proof, and Linial only at second hand.
- **I did not re-derive `γ_i ≥ 1/2` from G‴ + L** (Q1's payoff clause), and I did not audit row G‴.
- **I did not open the Lean artifact** for R2's residual width-3 risk, and this is a LaTeX reading,
  not a machine check.
- **I ran no code.** No script, no enumeration, no data file. `δ(E) = 1/3` is a three-extension hand
  count; the 166-refuter and `0/132` figures are read from the two probe documents and **not
  re-measured** — §1.5's finding is that their *frames* differ, which is a reading of what each
  document states about itself, not a re-run.
- **Q1's sweep is a `grep` sweep, not a proof of absence.** I searched both repositories'
  `docs/`, `STATE.md` and `*.tex` for `antichain` co-occurring with
  `consecutive|adjacent|contiguous`, and for `antichain` with `linear extension`. A statement of the
  lemma phrased without any of those words would be missed.
- **I did not sweep the other 57 of the 76 ledger rows.** ae768 classified 19 and said so; I
  touched rows 3a, 3b, 5, 6, 7, 8, and G‴, and no others.
- **§1.5's consequence for row 3b's `FP` mark is stated, not landed.** Whether the row should be
  re-marked, restated conditionally, or split is a `STATE.md` judgement in the other repository and
  is pm-onethird's call.
