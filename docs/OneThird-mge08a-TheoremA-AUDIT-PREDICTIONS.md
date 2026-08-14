# mg-e08a — audit predictions for mg-52c4's Theorem A / Corollary B

**Committed BEFORE any audit code exists.** Written after reading, on paper only:
`docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` (all of it), the F17 §3 forward pointer and
F28 §1.6/§2.3 edits landed by `cf63bb3`, and F17 §0.2/§2.1–§2.3. **No script was written, run, or
read at the time of this commit** — `scripts/compat_geom_mg52c4_subposet_complexes.py` was
deliberately *not* opened, so that the audit instrument is an independent re-implementation and not a
re-reading of the instrument under audit.

The point of pre-registering: an audit that writes its predictions after seeing its own output
cannot be caught being wrong. These can be.

---

## Group A — the two named proof steps (§2.4 names them)

- **A1.** *(join-irreducibility of covers under `tc`)* The step *"if `(x,y) ∈ tc(S)` with `(x,y)` a
  cover of `P`, then `(x,y) ∈ S`"* is **CORRECT**, and its correctness depends on the unstated but
  satisfied side condition `S ⊆ P`. **Prediction: correct; the side condition holds at every use
  site (`S = Q ∪ {v} ⊆ P`); no repair needed.**
- **A2.** *(`κ`'s image nonempty and proper)* **Prediction: correct.** `{v}` is transitively closed,
  nonempty, and proper; the properness argument (`Cov(P) ≠ ∅`, `v ∉ Cov(P)` ⟹ `c ≥ 2`) is valid.
- **A3.** *(the rest of (A1))* `κ` extensive / monotone / idempotent, image = fixed-point set
  `{Q : v ∈ Q}` with global minimum `{v}`, Björner §10.2. **Prediction: all correct; (A1) stands.**
- **A4.** *((A2), the height-1 half)* "no 3-chain ⟹ no composable pair ⟹ every subset of `Comp(P)`
  is transitively closed ⟹ `L(P) = 2^{Comp(P)}`". **Prediction: correct; (A2) stands.**
- **A5.** *(the crosscut cross-check in §2.3)* `Γ = {A ⊆ Comp(P) : Cov(P) ⊄ A}`, cone with apex `v`
  or `∂Δ^{c-1}`. **Prediction: correct, and genuinely independent of the closure-operator route.**
- **A6.** **Prediction: I will find NO error in Theorem A.** Stated flatly so that finding one
  counts as this prediction failing.

## Group B — the height-1 / 3-chain boundary and the degenerate cases

- **B1.** The trichotomy of stated equivalences *(3-chain ⟺ `Cov(P) ≠ Comp(P)` ⟺ `height(P) ≥ 2`)*
  is **correct under the edge-count height convention** (a 3-element chain has height 2) and the
  document uses that convention consistently. **Prediction: consistent, no error.**
- **B2.** The dichotomy is **exhaustive** given the hypothesis "at least one strict relation":
  height ≥ 1 always, so (A1) ∪ (A2) covers everything. **Prediction: exhaustive.**
- **B3.** `c = 1` lands in (A2) with `Δ(L̄(P)) = ∅ = S^{-1}`; `c = 2` gives `S^0`.
  **Prediction: both correct, and `c = 1` is a genuine element of `PPF_n` (the single-relation
  minimal vertices), not a vacuous corner.**
- **B4.** **Antichains and isolated elements are NOT a gap.** `L̄(P)` depends on `P` only through
  `Comp(P)`, so isolated elements are invisible; the pure antichain (`Comp(P) = ∅`) is excluded by
  hypothesis and is not an element of `PPF_n` anyway. **Prediction: no degenerate case lands on the
  wrong side.**

## Group C — my own independent recomputation

- **C1.** An independent re-implementation (my own `tc`, my own order-complex builder, my own
  boundary-rank routine — **not** importing `compat_geom_F17_equivariant_morse.reduced_betti`, which
  the audited script imports) will reproduce Theorem A's prediction with **0 failures** over every
  poset on `≤ 5` elements.
- **C2.** The census figures will reproduce **exactly**: `|PPF_n| = 12, 194, 4110, 129302` for
  `n = 3,4,5,6`; height-≥2 / height-1 splits `0/12`, `108/86`, `3270/840`, `117660/11642`.
- **C3.** **I will push FULL reduced Betti past `n = 4`** — the boundary the audited doc admits at
  §2.4. **Prediction: at least 3500 of the 4110 posets of `PPF_5` are within a materialisable
  simplex cap**, so the `n = 5` gap is closed for the large majority by Betti, not by Euler.
- **C4.** Theorem A is a statement about an *arbitrary* finite poset, so `|Comp(P)|` — not `n` — is
  what bounds the computation. **Prediction: I can verify (A2) at `c` strictly larger than any `c`
  reachable inside `PPF_4`, by testing abstract height-1 posets directly.**

## Group D — the Euler/Möbius blindness (the stated verification gap)

- **D1.** **The gap is real as stated.** T1 (Möbius = predicted reduced Euler characteristic) cannot
  distinguish contractible from a wedge with cancelling Betti numbers. **Prediction: I will exhibit
  an explicit finite complex with `χ̃ = 0` that is NOT contractible, and show my Euler predicate
  passes it while my Betti predicate fails it.** If I cannot build one, D1 fails.
- **D2.** **But the gap is not load-bearing**, because Theorem A's proof is `n`-independent: it is
  about an arbitrary finite poset and never mentions `n`. **Prediction: the proof genuinely covers
  `n ≥ 5`; the corpus is NOT relying on the check that cannot see, once the proof is sound.**
  D1 and D2 are both predicted true and are not in tension: D1 says the *instrument* is blind, D2
  says the *instrument is not what is carrying the claim*.

## Group E — Corollary B: theorem or regime claim?

- **E1.** **Corollary B is a THEOREM, not a regime claim**, for the class it names: for *every*
  `P ∈ PPF_n` of height ≥ 2, `lk_{Δ_n}(P)` is contractible, with no `n` bound and no width bound.
  **Prediction: theorem.**
- **E2.** The Mirsky step (height-1 + width ≤ 3 ⟹ `≤ 6` elements ⟹ `n ≥ 7` forces a 3-chain) is
  **correct**. **Prediction: correct.**
- **E3.** **The load-bearing sentence is nonetheless narrower than it reads.** The vertices of `Δ_n`
  are *all* of `PPF_n`, and the height-1 vertices are a positive fraction of `PPF_n` at every `n`
  (9.0% at `n = 6` by the doc's own census) — they are *not* width ≤ 3, which is the only thing
  Mirsky removes. So *"the fibrewise anchor is identically zero in the width-3 / `n ≥ 7` regime"*
  is a theorem **about the width-≤3 vertices**, not about the fibrewise structure of `Δ_n`.
  **Prediction: I will exhibit at least one height-1 `P ∈ PPF_4` whose FULL link
  `Δ(L̄(P)) * Δ(↑P ∖ {P})` is NOT contractible** — i.e. Corollary B's conclusion is false off the
  height-≥2 class, so the class matters and "identically" is doing more work than the theorem
  licenses.
- **E4.** The audited doc's T3 reports *"108/108 height-≥2 links contractible"* over `PPF_4` and
  **reports nothing about the other 86**. **Prediction: the 86 height-1 links were computed by the
  same test and their result is simply not in the table**, i.e. this is a reporting omission rather
  than an uncomputed case. (If the audited script turns out never to have computed them, E4 fails
  and the omission is worse than predicted.)

## Group F — the uncomputed upper link `Δ(↑P ∖ {P})`

- **F1.** The doc's §3.5 argument (*"it is not something `ω_bal` restricts to"*) is **CORRECT and
  can be strengthened**: `Δ(↑P ∖ {P}) ⊆ Δ(↑P) ⊆ Δ_n` and `Δ(↑P)` is a cone, so the restriction of
  `ω_bal` to the upper link **factors through zero for every `P`, with no height hypothesis at all**.
  **Prediction: correct; the height-≥2 hypothesis §3.5 inherits from §3.3 is not needed for this
  half.**
- **F2.** **But the restriction map is not the only map to the link.** The Mayer–Vietoris /
  deletion sequence supplies `∂ : H̃_{n-2}(Δ_n) → H̃_{n-3}(lk_{Δ_n}(P))`, which is **not** a
  restriction and is **not** covered by F1's cone argument. At height-≥2 vertices Corollary B kills
  it; at height-1 vertices nothing in the document does. **Prediction: this map is not addressed
  anywhere in the audited document.**
- **F3.** **Prediction (lower confidence, recorded as a genuine risk of being wrong): I will find at
  least one `P ∈ PPF_4` with `H̃_*(Δ_4 ∖ {P}) ≠ H̃_*(Δ_4)`** — a vertex at which the F17+F18 class
  *is* locally visible. If every deletion preserves the homology, F3 fails and the "identically
  trivial" headline survives a test it could have failed.

## Group G — §4's "buys nothing"

- **G1.** §4 point 4 (*"where a sphere does appear it is blind — `S^{c-2}` depends only on
  `|Comp(P)|`"*) is a statement about `Δ(L̄(P))`, the **lower factor**. The object F28 §2.3 / F29-B
  actually asks about is `lk_{Δ_n}(P)`, whose type at a height-1 vertex is
  `Σ^{c-1} Δ(↑P ∖ {P})` — **not** a function of `c` alone. **Prediction: the blindness argument does
  not transfer to the link, and the document conflates the two objects at this point.**
- **G2.** §4's two walls (F28 sheaf wall, F31 kernel wall) are correctly identified as untouched by
  a change of base complex. **Prediction: correct.**
- **G3.** §4's final paragraph (Corollary B does *not* localise the Garland spectral defect, because
  contractible ⇏ spectral gap) is **correct and is the document's most careful moment**.
  **Prediction: correct.**
- **G4.** Overall verdict prediction: **Theorem A and Corollary B are SOUND; the "buys nothing"
  recommendation is CORRECT for the direction it names; but the headline sentence
  "identically zero" over-reaches its own theorem at the height-1 vertices, and the document should
  be scoped rather than retracted.** Recorded flatly so a different outcome is visible as a miss.

## Group H — controls on my own instrument

- **H1.** My reduced-Betti routine will reproduce known answers on independently-known complexes:
  `∂Δ^k ≃ S^{k-1}` for `k = 1..4`, a triangulated torus `(1,2,1)`, a triangulated Klein bottle
  (`(1,1,0)` over `Q`, differing mod 2), and the empty complex (`H̃_{-1} = Q`).
  **Prediction: all reproduce.**
- **H2.** **Swapped-prediction control:** asserting (A1)'s answer for height-1 posets and (A2)'s for
  height-≥2 posets must go RED on **100%** of both classes wherever the two predictions differ.
  **Prediction: 100% both directions.**
- **H3.** **Perturbation control (the one this ticket demands):** take a height-1 poset `P` covered
  by (A2), add one relation that creates a 3-chain, and confirm the measured homotopy type flips
  from `S^{c-2}` to contractible and that my checker *reports the flip*. Symmetrically, delete a
  relation from a height-≥2 poset to reach height 1 and confirm the flip back.
  **Prediction: both flips detected; a checker that could not see them would pass H2 anyway, which
  is why H3 is separate from H2.**
- **H4.** My instrument shares one thing with the audited one: both compute homology of an order
  complex. **Prediction: the shared-failure enumeration will find exactly one non-independent
  ingredient — the definition of `tc` — and I will control it by checking my `tc` against the
  fixed-point characterisation `Q = tc(Q)` on every poset I generate, not against theirs.**

---

*No code existed when this file was committed. Audit instrument:
`scripts/compat_geom_mge08a_theoremA_audit.py` (to be written next).*
