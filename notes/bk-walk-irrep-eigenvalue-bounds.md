> **EXPLORATORY NOTE — Daniel's working scratch.** Not a formal claim or
> proof commitment. Saved for reference per the mg-cda8-style
> audit-as-deliverable framing. May be wrong / incomplete / superseded.

# BK walk on $S_n$ — eigenvalue bounds by non-trivial irrep / character analysis

**Context.** This is for the walk of linear extensions on $S_n$.

| Non-trivial irrep $\rho$ | What its character measures | What to check on the family of posets | Bound produced |
|---|---|---|---|
| **Sign representation** $[1^n]$ | parity of the permutation | **sign-imbalance** $\Sigma(P) = \sum_{g \in G_P} (-1)^{\operatorname{sgn}(g)}$ | $\lvert \lambda_{\text{sign}} \rvert = \frac{\lvert \Sigma(P) \rvert}{\lvert G_P \rvert} \leq \delta$ → gap $\geq (1 - \delta)$ |
| **Standard representation** $[n-1, 1]$ | "how many fixed points" ($\chi(g) = \operatorname{fix}(g) - 1$) | **expected number of fixed points** in a *uniform* random linear extension | $\lvert \lambda_{\text{std}} \rvert \leq \frac{\mathbf{E}[\operatorname{fix}] - 1}{n - 1}$ |
| **Two-row representation** $[n-2, 2]$ | "how many 2-cycles" ($\chi(g) = \#\text{2-cycles} - 1$) | **expected number of 2-cycles** $= \frac{1}{2} \sum_{i \neq j} \Pr(i \leftrightarrow j)$ | $\lvert \lambda_{[n-2, 2]} \rvert \leq \frac{\mathbf{E}[\#\text{2-cycles}] - 1}{n (n-3) / 2}$ |

---

**Related ticket.** mg-ea39 (Daniel's conceptual-development workspace) — this
note is an input to that work.
