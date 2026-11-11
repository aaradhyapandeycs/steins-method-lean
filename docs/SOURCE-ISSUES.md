# Source Issues, Errata, Underspecifications, and Counterexamples (`arXiv:1109.1880v1`)

Per Rules 3–5 of [`AGENTS.md`](../AGENTS.md) and [`docs/AUTHOR_RULINGS.md`](AUTHOR_RULINGS.md) (`RULING-USER-2026-11-11`), this single ledger records every source typo, cross-reference bug, underspecification, and false-as-printed statement in Nathan Ross, *"Fundamentals of Stein's method"* (`SteinIntro.tex`, SHA-256 `02041ab1408158cebf82f2ec67fed7722ed7594b78728ca00d644a92d67d8d95`), together with verified counterexamples and the exact `_corrected` or `_restricted` Lean statement names declared in `Formalization/Statements/SecN.lean` (and proved in `Formalization/Statements/SecNProofs.lean`). Part III records unnumbered prose, proof, and reading notes whose numbered theorem statements are formalized literally without `_corrected` or `_restricted` suffixes.

---

## Part I — Source Typos and Cross-Reference Errata

### `ISSUE-TYPO-1.1` — Indicator Notation Typo and Stray Byte in Total Variation Definition
- **Source**: Section 1.1.1, item 3 (`SteinIntro.tex:520-521`)
- **Printed text**: `"By taking \mathcal{H}=\{\mathbb{I}[A\in\mathbb{R}]: A \in\mbox{Borel}(\mathbb{R})\} in (1.1), we obtain the total variation metric... We will use the total variation metric for approximation by Œdiscrete distributions."`
- **Issue**: `\mathbb{I}[A\in\mathbb{R}]` is a typo for the indicator function `\mathbb{I}[\cdot \in A]` (`A.indicator 1`), and `L521` contains a stray Latin-1 ligature byte (`0x8C`, `Œ`) before `discrete`.
- **Resolution**: `SteinMethod.tvDist` is defined via `{h : α → ℝ | ∃ A, MeasurableSet A ∧ h = A.indicator 1}` (`D1`, `D3`).

### `ISSUE-TYPO-3.3` — Summand Index Typo in Lemma 3.3
- **Source**: Lemma 3.3 (`\label{lem33}`, `SteinIntro.tex:754`)
- **Printed text**: `"In the notation of Theorem \ref{thm32}, if W_i = (\sum_{j\not=i} X_i)/\sqrt{n} then..."`
- **Issue**: Summing $X_i$ over $j \ne i$ yields $(n-1)X_i/\sqrt{n}$, which is neither independent of $X_i$ (`L766`) nor satisfies $W - W_i = X_i/\sqrt{n}$ (`L788`). The intended summand is $X_j$: $W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$.
- **Resolution**: Formalize Lemma 3.3 with $W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$ (equivalently $W - X_i/\sqrt{n}$).

### `ISSUE-TYPO-3.2.1` — Metric Symbol Typo in Section 3.2.1
- **Source**: Section 3.2.1 (`SteinIntro.tex:936`)
- **Printed text**: `"\dk(W, Z) \le ..."` when applying Theorem 3.5 (`\label{thm41}`) to triangle counts in $G(n, p)$.
- **Issue**: Theorem 3.5 bounds the Wasserstein distance $\dw(W, Z)$, not $\dk(W, Z)$.

### `ISSUE-TYPO-3.4a` — Missing Expectation Operator in Display `(3.23)`
- **Source**: Section 3.4, display `(3.23)` (`\label{71}`, `SteinIntro.tex:1232-1236`)
- **Printed text**: `\mathbb{E}[W f(W)] = \frac{\mu}{\sigma}\left[f\left(\frac{X^s-\mu}{\sigma}\right) - f\left(\frac{X-\mu}{\sigma}\right)\right]`.
- **Issue**: The right-hand side is a random variable whereas the left-hand side is deterministic; `\mathbb{E}` is omitted before the bracket on the right-hand side.
- **Resolution**: Formalize `Sec3_4_sizeBias_identity` with expectation on the right-hand side (together with `Integrable (fun ω ↦ f ((Xs ω - μ) / σ)) P`).

### `ISSUE-TYPO-3.15` — Cross-Reference `\ref{71}` Instead of `\ref{cor71}` in Proof of Corollary 3.15
- **Source**: Proof of Corollary 3.15 (`\label{cor71}`, `SteinIntro.tex:1341`)
- **Printed text**: `"Corollary \ref{71} is obvious since due to independence, the conditioning in the construction has no effect."`
- **Issue**: `\ref{71}` is the equation label of display `(3.23)` (`SteinIntro.tex:1235`), so LaTeX prints `"Corollary 3.23"` instead of `"Corollary 3.15"` (`\ref{cor71}`).

### `ISSUE-TYPO-3.9` — Cross-Reference `\ref{ex71}` Instead of `\ref{ex72}` After Example 3.9
- **Source**: Remark following Example 3.9 (`SteinIntro.tex:1429`)
- **Printed text**: `"Example \ref{ex71} can be generalized to counts of vertices of a given degree d at some computational expense \cite{gol10, gori96}; related results pertain to the number of subgraphs counts in an \ER\ graph..."`
- **Issue**: `\ref{ex71}` is Example 3.8 (`SteinIntro.tex:1349-1353`, the normalized sum of independent variables left as an exercise), whereas isolated vertices in $G(n, p)$ (degree-$0$ vertices) is Example 3.9 (`\label{ex72}`, `SteinIntro.tex:1354-1427`).

### `ISSUE-TYPO-3.21` — Omitted Expectations `\IE[...]` and Derivative Prime `'` in Proof Display of Proposition 3.21
- **Source**: Proof of Proposition 3.21 (`\label{prop81}`, `SteinIntro.tex:1545-1549`)
- **Printed text (verbatim, `L1545-1549`)**:
  ```tex
  \ba
  \IE[Wf(W)]&=\sum_{i=1}^n X_i f(W-X_i +X_i) \\
  	&=\sum_{i=1}^n \sigma_i^2 f(W-X_i +X_i^z) \\
  	&=\IE[f'(W-X_I+X_I^z)].
  \ee
  ```
- **Issue**: Both `L1546` and `L1547` omit `\IE[...]` inside the sum, and `L1547` omits the derivative prime `'` on `f` (intended: `\sum_{i=1}^n \IE[X_i f(W-X_i +X_i)] = \sum_{i=1}^n \sigma_i^2 \IE[f'(W-X_i +X_i^z)]`). Proposition 3.21 (`Prop3_21`) itself is unaffected.

### `ISSUE-TYPO-3.27` — Cross-References `\ref{thm91}` (`L1741`) and `\ref{91}` (`L1775`) in Section 3.6
- **Source**: Remark following Theorem 3.27 (`SteinIntro.tex:1741-1743`) and proof of Theorem 3.28 (`SteinIntro.tex:1775`)
- **Printed text**:
  - `L1741-1742`: `"Theorem \ref{thm91} can be applied to sums of independent random variables which are almost surely bounded (note that $W$ bounded implies $W^z$ bounded),"`
  - `L1775`: `"and we can apply Lemma \ref{91} to find that the absolute value of \eq{911} is bounded above by"`
- **Issue**: At `L1741`, `\ref{thm91}` resolves to Theorem 3.24, whereas the unlabeled zero-bias Kolmogorov theorem immediately preceding it (`SteinIntro.tex:1697-1704`, Theorem 3.27) is the intended target (as shown by the parenthetical reference to $W^z$). At `L1775`, `\ref{91}` is the equation label `(3.38)` (`SteinIntro.tex:1669`), so LaTeX prints `"Lemma 3.38"` instead of `"Lemma 3.25"` (`\ref{lem91}`).

### `ISSUE-TYPO-4.4` — Missing Forward-Difference Operator `\Delta` in Proof of Lemma 4.4
- **Source**: Proof of Lemma 4.4 (`\label{lem103}`, `SteinIntro.tex:1901`)
- **Printed text**: `\Delta f_A(k) = \sum_{j \in A} f_j(k)`.
- **Issue**: Since $f_A(k) = \sum_{j \in A} f_j(k)$, taking $\Delta$ gives $\Delta f_A(k) = \sum_{j \in A} \Delta f_j(k)$; `\Delta` is omitted inside the sum on `L1901` (though the surrounding argument on `L1896-1905` uses the sign of $\Delta f_j(k)$).

### `ISSUE-TYPO-4.6` — Misplaced `\label{thm102}` Prints `"Theorem 4.1"` Instead of `"Theorem 4.6"`
- **Source**: Theorem 4.6 (`SteinIntro.tex:1942-1949`) and cross-references at `SteinIntro.tex:1969, 1983, 1989`
- **Printed text**: `\end{theorem}\label{thm102}` (`L1949`), causing `\ref{thm102}` at `L1969` (`"generalize Theorem 4.1"`), `L1983` (`"mimic the proof of Theorem 4.1 up to (4.5)"`), and `L1989` (`"As in the proof of Theorem 4.1"`) to print `"Theorem 4.1"` in the compiled PDF.
- **Issue**: Because `\label{thm102}` is placed outside `\begin{theorem}...\end{theorem}`, LaTeX binds `thm102` to the enclosing subsection counter (`4.1`) rather than Theorem 4.6.
- **Resolution**: `docs/source-inventory.md` records `thm102` on Theorem 4.6 (`L1942-1949`), its intended target.

### `ISSUE-TYPO-6.2` — Missing Subscript `A` in `\Delta f(k)` in Lemma 6.2
- **Source**: Lemma 6.2 (`\label{lem174}`, `SteinIntro.tex:3243-3249`)
- **Printed text (verbatim)**:
  ```tex
  \begin{lemma}\label{lem174}
  If $Z\sim\Geo(p)$, $A\subseteq \IN\cup\{0\}$, and $f_A$ is the unique solution with $f_A(0)=0$ of
  \ba
  (1-p)\Delta f_A(k)-p f_A(k)=\I[k\in A]-\IP(Z\in A),
  \ee
  then $-1\leq \Delta f(k) \leq 1$.
  \end{lemma}
  ```
- **Issue**: Line 3248 prints `\Delta f(k)` in place of `\Delta f_A(k)` (confirmed by the proof at `L3271`, `\Delta f_A(k)=\I[k\in A]-p\sum_{i\in A, i\geq k+1} (1-p)^{i-k-1}`). Formalized with `geomSteinSol p A` in `SteinMethod.Lem6_2`.

### `ISSUE-TYPO-6.6` — Spurious Superscript `W^{e_0}` in Proof of Theorem 6.6
- **Source**: Proof of Theorem 6.6 (`\label{thm1716}`, `SteinIntro.tex:3381-3383`)
- **Printed text (verbatim)**:
  ```tex
  \bes
     \IE W \IE \D f(W^{e_0})=\IE f(W).
  \ee
  ```
- **Issue**: `W^{e_0}` is a typo for `W^e` (defined at `L3359` and used at `L3384`). Theorem 6.6 (`Thm6_6`) itself is unaffected.

### `ISSUE-TYPO-7.5` — Subscript Typo `a_{i \sigma_j}` in Example 7.5 (Hoeffding's Combinatorial CLT)
- **Source**: Example 7.5 (`SteinIntro.tex:3602, 3607`)
- **Printed text**: `W = \sum_{i=1}^n a_{i \sigma_j} - \frac{1}{n}\sum_{i,j} a_{i j}` (`L3602`) and `W' = \sum_{i=1}^n a_{i \sigma'_j} - \frac{1}{n}\sum_{i,j} a_{i j}` (`L3607`), with $j$ unbound in the first sum.
- **Issue**: Confirmed by `L3621` (`a_{i \sigma_i}`), the intended definitions are $W = \sum_{i=1}^n a_{i, \sigma(i)} - \frac{1}{n}\sum_{i,j} a_{i j}$ and $W' = \sum_{i=1}^n a_{i, \sigma'(i)} - \frac{1}{n}\sum_{i,j} a_{i j}$.

---

## Part II — Mathematical Source Issues, Underspecifications, and Counterexamples

### `ISSUE-2.1` — Unbound `Z` in Lemma 2.1(2) (Earlier Moment Counterexample Withdrawn)
- **Source**: Lemma 2.1(2) (`\label{lem1}`, `SteinIntro.tex:570-572`)
- **Printed text**: *"If for some random variable $W$, $\mathbb{E}\mathcal{A}f(W) = 0$ for all absolutely continuous functions $f$ with $\mathbb{E}|f'(Z)| < \infty$, then $W$ has the standard normal distribution."*
- **Issue**: The variable $Z$ is not bound inside item 2; from item 1 (`L568`), $Z$ denotes a standard normal random variable ($Z \sim \mathcal{N}(0, 1)$).
- **Note on withdrawn moment objection (`review-00-setup.md` H2)**: An earlier draft claimed heavy-tailed $W$ (e.g. Cauchy) required an added integrability hypothesis because $f \equiv 1$ gives $\mathcal{A}f(w) = -w$. That objection is **withdrawn**: the hypothesis quantifies over *all* locally absolutely continuous $f$ with $\mathbb{E}|f'(Z)| < \infty$, which includes every smooth Stein solution $f_h$ for $h \in C_b^1(\mathbb{R})$, for which $\mathcal{A}f_h(W) = h(W) - \Phi(h)$ is bounded and integrable for *every* random variable $W$ regardless of moments.
- **Resolution (`D5`)**: State `Lem2_1_2` as printed, binding $Z \sim \mathcal{N}(0, 1)$ via `Integrable (deriv f) stdNormalLaw` and assuming only `AEMeasurable W P` on `[IsProbabilityMeasure P]`. No `_corrected` variant is needed.

---

### `ISSUE-2.2` — Non-Differentiability at Jump Discontinuities and Left-Derivative Uniqueness Failure Without Continuity
- **Source**: Lemma 2.2 (`\label{lem2}`, `SteinIntro.tex:578-588`), Corollary 2.3 (`\label{cor1}`, `SteinIntro.tex:591-596`), the `"let f_h solve"` premise of Proposition 2.4 (`\label{prop31}`, `SteinIntro.tex:659-670`), the preamble of Lemma 2.5 (`\label{lem31}`, `SteinIntro.tex:674-684`), Theorem 3.24 (`\label{thm91}`, `SteinIntro.tex:1666-1675`), and Lemma 3.25 (`\label{lem91}`, `SteinIntro.tex:1677-1686`)
- **Printed text (verbatim)**:
  - Lemma 2.2 (`L579-587`): *"If $\Phi(x)$ is the c.d.f. of the standard normal distribution, then the unique bounded solution $f_x$ of the differential equation $f'_x(w)-wf_x(w)=\mathbb{I}[w\leq x] - \Phi(x)$ is given by $f_x(w)=e^{w^2/2}\int_w^{\infty} e^{-t^2/2}\left(\Phi(x)-\mathbb{I}[t\leq x]\right) dt = -e^{w^2/2}\int_{-\infty}^w e^{-t^2/2}\left(\Phi(x)-\mathbb{I}[t\leq x]\right) dt$."*
  - Corollary 2.3 (`L592-595`): *"If $f_x$ is as defined in Lemma \ref{lem2}, then for any random variable $W$, $|\mathbb{P}(W\leq x) - \Phi(x)|= |\mathbb{E}[f'_x(W)-Wf_x(W)]|$."*
  - Proposition 2.4 (`L659-670`): *"More generally, for a given function $h$ ... let $f_h$ solve the differential equation $f_h'(w)-wf_h(w)=h(w)-\Phi(h)$ ... If $W$ is a random variable and $Z$ has the standard normal distribution, then $d_{\mathcal{H}}(\mathcal{L}(W),\mathcal{L}(Z)) = \sup_{h\in\mathcal{H}}\bigl|\mathbb{E}[f_h'(W)-Wf_h(W)]\bigr|$."*
  - Lemma 2.5 preamble (`L675-684`): *"For a given function $h$, the solution $f_h$ to (2.6) (`f_h'(w)-wf_h(w)=h(w)-\Phi(h)`) is given by $f_h(w)=e^{w^2/2}\int_w^\infty e^{-t^2/2}(\Phi(h)-h(t))\,dt = -e^{w^2/2}\int_{-\infty}^w e^{-t^2/2}(\Phi(h)-h(t))\,dt$."*
  - Theorem 3.24 (`L1667-1674`): *"Let $\Phi$ denote the standard normal distribution function and let $f_x(w)$ be the unique bounded solution of $f_x'(w)-wf_x(w)=\mathbb{I}[w\leq x]-\Phi(x)$. If $W$ is a random variable with finite mean and $Z$ is standard normal, then $d_{\mathrm{K}}(W,Z)=\sup_{x\in\mathbb{R}}|\mathbb{E}[f_x'(W)-Wf_x(W)]|$."*
  - Lemma 3.25 (`L1678-1685`): *"If $f_x$ is the unique bounded solution to (3.38), then $\|f_x\| \le \sqrt{\frac{\pi}{2}}$, $\|f_x'\| \le 2$, and for all $u, v, w \in \mathbb{R}$, $|(w+u)f_x(w+u)-(w+v)f_x(w+v)| \le (|w|+\sqrt{2\pi}/4)(|u|+|v|)$."*
- **Counterexample 1 (non-existence under the two-sided derivative, and failure of the `deriv` + `normalSteinSolKolm` transcription at $W \equiv 0$)**:
  - Fix $x = 0$ and let $f_0 = \mathrm{normalSteinSolKolm}\,0$. From `SteinIntro.tex:616-623`, $\lim_{w \uparrow 0} f_0'(w) = 1 - \Phi(0) = 1/2$, whereas $\lim_{w \downarrow 0} f_0'(w) = -\Phi(0) = -1/2$. By Darboux's intermediate-value theorem for derivatives, **no** function $f : \mathbb{R} \to \mathbb{R}$ satisfies the two-sided differential equation `HasDerivAt f (w * f w + (Set.Iic x).indicator 1 w - stdNormalCDF x) w` for all $w \in \mathbb{R}$ (and likewise, for any bounded $h$ with a jump discontinuity as in Lemma 2.5(1), Darboux's theorem rules out an everywhere two-sided differentiable solution of `(2.6)`). Under the two-sided reading, no $f_x$ exists at all, so the printed Corollary 2.3 and Theorem 3.24 refer to a nonexistent object rather than being refuted (and Proposition 2.4's everywhere-ODE premise is vacuous on classes containing functions with jumps).
  - What fails numerically at $W \equiv 0$ is the Lean transcription that pairs two-sided `deriv` (`normalSteinOp`) with the integral formula `normalSteinSolKolm`: in Lean `deriv f_0 0 = 0`, so at $W \equiv 0$ and $x = 0$,
    $$\bigl|\mathbb{E}[\mathrm{deriv}\,f_0(W) - W f_0(W)]\bigr| = |0 - 0| = 0 \ne \frac{1}{2} = |\mathbb{P}(W \le 0) - \Phi(0)|,$$
    refuting the transcription that uses `deriv` together with `normalSteinSolKolm`.
  - Both claims are machine-checked in `Formalization/Normal/KolmogorovSolution.lean` as `SteinMethod.Lem2_2_twoSided_noSolution` and `SteinMethod.Cor2_3_twoSided_counterexample`.
- **Counterexample 2 (`review-01.md` Finding `H3` — non-uniqueness under the left-derivative reading without continuity)**:
  - Even when $f_x'(w)$ in `(2.1)` (`L581`) is read as the left derivative (`HasDerivWithinAt … (Set.Iic w) w`, per Chen–Goldstein–Shao 2011, p. 15 and `D4`), uniqueness among bounded functions fails unless **continuity** is required. Fix any $a < b$ in $\mathbb{R}$ and define
    $$h(w) := e^{w^2/2}\,\mathbf{1}_{(a, b]}(w).$$
  - *Boundedness*: For $w \notin (a, b]$, $h(w) = 0$; for $w \in (a, b]$, $w^2 \le \max(a^2, b^2)$, so $|h(w)| \le e^{\max(a^2, b^2)/2}$ for all $w \in \mathbb{R}$.
  - *Left-differentiability everywhere with left derivative $w h(w)$* (`∀ w, HasDerivWithinAt h (w * h w) (Set.Iic w) w`):
    1. **For $w \le a$**: $(-\infty, w] \subseteq (-\infty, a]$, on which $h \equiv 0$, so `HasDerivWithinAt h 0 (Set.Iic w) w` holds and $0 = w h(w)$.
    2. **For $a < w \le b$**: Because $a < w$, $(a, w] = (a, \infty) \cap (-\infty, w]$ is a neighborhood of $w$ within `Set.Iic w` contained in $(a, b]$ (note that this includes the right endpoint $w = b$, where $(a, b] = (a, \infty) \cap (-\infty, b]$). On $(a, w]$, $h(t) = e^{t^2/2}$ identically, whose derivative at $w$ is $w e^{w^2/2} = w h(w)$; hence `HasDerivWithinAt h (w * h w) (Set.Iic w) w` holds for all $w \in (a, b]$.
    3. **For $w > b$**: Because $b < w$, $(b, w] = (b, \infty) \cap (-\infty, w]$ is a neighborhood of $w$ within `Set.Iic w` disjoint from $(a, b]$, on which $h \equiv 0$; hence `HasDerivWithinAt h 0 (Set.Iic w) w` holds and $0 = w h(w)$.
  - Since $f_x = \mathrm{normalSteinSolKolm}\,x$ is bounded and satisfies `HasDerivWithinAt f_x (w * f_x w + (Set.Iic x).indicator 1 w - stdNormalCDF x) (Set.Iic w) w` for all $w \in \mathbb{R}$, linearity of `HasDerivWithinAt` shows that $g := f_x + h$ (with $g(b) = f_x(b) + e^{b^2/2} \ne f_x(b)$) is a **second** bounded solution of the left-derivative Stein equation `(2.1)`.
  - *Restoration of uniqueness with `Continuous`*: If $g$ is bounded, **continuous** on $\mathbb{R}$, and satisfies `∀ w, HasDerivWithinAt g (w * g w + (Set.Iic x).indicator 1 w - stdNormalCDF x) (Set.Iic w) w` (using the genuine one-sided derivative predicate `HasDerivWithinAt`, not a junk-value equation in `derivWithin`), then $d := g - f_x$ is bounded, continuous, and has continuous left derivative $w \mapsto w d(w)$ everywhere, hence is two-sided differentiable on $\mathbb{R}$ with $d'(w) = w d(w)$, forcing $d(w) = C e^{w^2/2}$ and $C = 0$ by boundedness.
- **Moment note (`review-00-setup.md` H3)**: By the Mills-ratio inequality, $|w f_x(w)| \le 1$ and the left derivative of $f_x$ is bounded on $\mathbb{R}$, so `normalSteinOpLeft f_x (W ω)` is bounded by $2$ and integrable for **every** random variable $W$ without any moment assumption.
- **Resolution (`D4`, `H3`)**:
  - `Lem2_2_corrected`: for every $x \in \mathbb{R}$, with `f_x := normalSteinSolKolm x`, asserts (a) `∃ B, ∀ w, |f_x w| ≤ B` (with library bound `√(π / 2)`), (b) `Continuous f_x`, (c) `∀ w, HasDerivWithinAt f_x (w * f_x w + (Set.Iic x).indicator 1 w - stdNormalCDF x) (Set.Iic w) w`, (d) `∀ w ≠ x, HasDerivAt f_x (w * f_x w + (Set.Iic x).indicator 1 w - stdNormalCDF x) w`, (e) `∀ w, f_x w = -Real.exp (w ^ 2 / 2) * ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalCDF x - (Set.Iic x).indicator 1 t)`, and (f) uniqueness: every bounded `Continuous` function `g` satisfying (c) equals `f_x`.
  - `Cor2_3_corrected`: for every `AEMeasurable W P` on `[IsProbabilityMeasure P]` and every $x \in \mathbb{R}$ (with **no** integrability hypothesis), `|P.real {ω | W ω ≤ x} - stdNormalCDF x| = |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P|`.
  - `Lem2_5_formula` and `Lem2_5_ode_contAt`: for measurable Gaussian-integrable $h$, `normalSteinSol h` satisfies the lower-tail integral representation everywhere, satisfies the two-sided Stein ODE everywhere when $h$ is continuous (`Lem2_5_formula`), and satisfies the two-sided Stein ODE at every continuity point $w$ of $h$ (`Lem2_5_ode_contAt`).
  - `Thm3_24_corrected` (keeping the printed `Integrable W P`) and `Lem3_25_corrected` likewise use the left-derivative formulation (`normalSteinOpLeft` / `derivWithin … (Set.Iic w) w`).

---

### `ISSUE-3.2.1` — Division by $\sigma = 0$ at Boundary Probabilities $p \in \{0, 1\}$ in Section 3.2.1
- **Source**: Section 3.2.1, triangle counts in $G(n, p)$ (`SteinIntro.tex:918-941`)
- **Printed text (verbatim, `L932-941`)**:
  - `L932`: `"\sigma^2:=\var(T)=\binom{n}{3}p^3[1-p^3+3(n-3)p^2(1-p)], "`
  - `L934-939`: `"and Theorem \ref{thm41} implies that for W=(T-\IE[T])/\sigma and Z a standard normal random variable \dk(W, Z) \le \frac{(3n-8)^2}{\sigma^3}\binom{n}{3}p^3(1-p^3)[(1-p^3)^2+p^6] + \frac{\sqrt{26}(3n-8)^{3/2}}{\sqrt{\pi}\sigma^2}\sqrt{\binom{n}{3}p^3(1-p^3)[(1-p^3)^3+p^9]}."`
  - `L941`: `"This bound holds for all n\geq 3 and 0\leq p \leq 1,"`
- **Counterexample / Boundary Defect**:
  - At $p = 0$ ($G(n, 0)$ empty, $T \equiv 0$) and at $p = 1$ ($G(n, 1) = K_n$, $T \equiv \binom{n}{3}$), $\sigma^2 = \mathrm{Var}(T) = 0$. Consequently, $W = (T - \mathbb{E}[T])/\sigma$ and both denominators $\sigma^3$ and $\sigma^2$ in `L937-938` divide by zero (and in Lean, `0 / 0 = 0` would collapse $W$ to the constant $0$, where $d_{\mathrm{W}}(\delta_0, \mathcal{N}(0, 1)) = \sqrt{2/\pi} > 0$, while evaluating the right-hand side of `L937-938` to `0`, making the Lean transcription literally false at $p \in \{0, 1\}$).
- **Resolution**: Formalize `Sec3_2_1_triangles_restricted` under `3 ≤ n`, `0 < p`, and `p < 1` (for which $\sigma > 0$), using `wassersteinDist` per `ISSUE-TYPO-3.2.1`.

---

### `ISSUE-3.5` — Singleton Dependency-Neighborhood Hypothesis Too Weak in Theorem 3.5
- **Source**: Definition 3.1 (`SteinIntro.tex:805-809`) and Theorem 3.5 (`\label{thm41}`, `SteinIntro.tex:815-822`, post-theorem note `L823-825`; proof counting step `(3.15)` `\label{43}` at `SteinIntro.tex:882-894`)
- **Printed text (verbatim)**:
  - Definition 3.1 (`L805-809`): *"We say that a collection of random variables $(X_1, \ldots, X_n)$ has dependency neighborhoods $N_i\subseteq \{1, \ldots, n\}$, $i=1, \ldots, n$, if $X_i$ is independent of $\{X_j\}_{j\not\in N_i}$."* (Note explicitly that Definition 3.1 does **not** require $i \in N_i$.)
  - Theorem 3.5 (`L816-821`): *"Let $X_1, \ldots, X_n$ be random variables with $\mathbb{E}[X_i^4] \lt \infty$, $\mathbb{E}[X_i]=0$, $\sigma^2=\mathrm{Var}\left(\sum_i X_i\right)$, and define $W=\sum_i X_i/\sigma$. Let the collection $(X_1, \ldots, X_n)$ have dependency neighborhoods $N_i$, $i=1, \ldots, n$, with $D:=\max_{1\leq i \leq n} |N_i|$. Then for $Z$ a standard normal random variable,*
    $$d_{\mathrm{W}}(W,Z)\leq \frac{D^2}{\sigma^3}\sum_{i=1}^n\mathbb{E}|X_i|^3+\frac{\sqrt{26}D^{3/2}}{\sqrt{\pi}\sigma^2}\sqrt{\sum_{i=1}^n\mathbb{E}[X_i^4]}.\text{''}$$
- **Counterexample**: Let $A_1, \dots, A_m, S$ be i.i.d. Rademacher($\pm 1$) random variables. Set $n = 2m$, $X_{2r-1} = A_r$, $X_{2r} = S A_r$, and $N_{2r-1} = N_{2r} = \{2r-1, 2r\}$ ($D = 2$, with $i \in N_i$ for every $i$) for $r = 1, \dots, m$.
  - *Check hypotheses*: $\mathbb{E}[X_i] = 0$, $\mathbb{E}[X_{2r-1} X_{2r}] = \mathbb{E}[S A_r^2] = 0$, and for $r \ne s$, $(A_r, S A_r)$ and $(A_s, S A_s)$ are uncorrelated ($\mathbb{E}[S A_r S A_s] = \mathbb{E}[A_r]\mathbb{E}[A_s] = 0$), so $\sigma^2 = 2m$. Moreover, for each fixed $r$, $X_{2r-1} = A_r$ is independent of $\{A_s, S A_s : s \ne r\}$, and $X_{2r} = S A_r$ is also independent of $\{A_s, S A_s : s \ne r\}$ because $(S A_r, (A_s, S A_s)_{s \ne r})$ has the exact product distribution of $2m - 1$ Rademachers (inverting $A_s \mapsto S A_s$ for $s \ne r$ preserves the i.i.d. Rademacher law conditional on $S$ and $A_r$). Thus Definition 3.1 holds with $D = 2$.
  - *Failure of conclusion*: The right-hand side of `(3.8)` (`L820`) is $\frac{4}{(2m)^{3/2}}(2m) + \frac{\sqrt{26}\cdot 2^{3/2}}{\sqrt{\pi}(2m)}\sqrt{2m} = O(m^{-1/2}) \to 0$ as $m \to \infty$. Yet $\sum_{i=1}^{2m} X_i = (1 + S)\sum_{r=1}^m A_r$ equals $0$ whenever $S = -1$ (probability $1/2$), so $W \stackrel{d}{\to} \frac{1}{2}\delta_0 + \frac{1}{2}\mathcal{N}(0, 2)$ and $d_{\mathrm{W}}(W, Z) \not\to 0$.
  - *Failing proof step*: In `(3.15)` (`\label{43}`, `SteinIntro.tex:882-894`), Ross splits $\sum_{i \ne j}\sum_{k \in N_i}\sum_{l \in N_j}\mathbb{E}[X_i X_j X_k X_l]$ into a first sum over index tuples where $\{X_i, X_k\}$ is independent of $\{X_j, X_l\}$ and a second sum over the remaining tuples, then bounds the second sum by $6 D^3 \sum_{i=1}^n \mathbb{E}[X_i^4]$ via index-tuple counting (`L890-891`: *"since the number of 'connected components' with at most four vertices of the dependency graph induced by the neighborhoods, is no more than $D \times 2D \times 3D$"*). Definition 3.1 alone neither requires $i \in N_i$ nor implies that $\{X_i, X_k\}$ is independent of $\{X_j, X_l\}$ outside the counted neighborhood tuples: in the $n = 2m$ construction above, $X_{2r-1} X_{2r} = S = X_{2s-1} X_{2s}$ for all $m(m-1)$ pairs $r \ne s$, so $\Theta(m^2)$ four-tuples fail independence rather than $O(D^3 m)$.
- **Resolution**: Formalize `Thm3_5_corrected` using the dependency-graph hypothesis `IsDependencyGraph P X N` (`(∀ i, i ∈ N i) ∧ (∀ i j, j ∈ N i → i ∈ N j) ∧ ∀ A B : Finset (Fin n), (∀ a ∈ A, ∀ b ∈ B, b ∉ N a) → ProbabilityTheory.IndepFun (fun ω (a : A) ↦ X a ω) (fun ω (b : B) ↦ X b ω) P`, matching `SteinIntro.tex:810-812`) together with `0 < ProbabilityTheory.variance (fun ω ↦ ∑ i, X i ω) P` (`0 < σ`, which is well-definedness because the source divides by $\sigma$ in $W = \sum_i X_i / \sigma$ and in `(3.8)`), while keeping the printed constant $\sqrt{26}$. `IsDependencyGraph.hasDependencyNeighborhoods` verifies that `IsDependencyGraph` strictly strengthens `HasDependencyNeighborhoods` (Definition 3.1), and `Thm3_5_counterexample` machine-checks the failure of the printed Theorem 3.5 under `HasDependencyNeighborhoods` at $m = 10^4$ ($n = 2 \times 10^4$, $D = 2$).

---

### `ISSUE-3.6` — Missing $1/n$ Proof-Step Factor at `L1074` and False i.i.d. $O(n^{-1/2})$ Remark at `L1091` in Example 3.6 (Printed Bound at `L1089` Proved for All $n \ge 1$)
- **Source**: Example 3.6 (`SteinIntro.tex:1053-1097`, specifically `L1072-1075`, `L1088-1090`, and `L1091`), applying Theorem 3.7 (`\label{thm51}`, `SteinIntro.tex:983-988`)
- **Printed text (verbatim)**:
  - Intermediate third-moment estimate (`L1072-1075`):
    ```tex
    \IE\abs{W'-W}^3&=\frac{1}{n^{3/2}}\sum_{i=1}^n\IE\abs{X_i-X_i'}^3 \\
    &\leq\frac{8}{n^{3/2}}\sum_{i=1}^n\IE\abs{X_i}^3,
    ```
  - Final Wasserstein bound (`L1088-1090`):
    ```tex
    \dw(W,Z)\leq \sqrt{\frac{2}{\pi}}\frac{\sqrt{\sum_{i=1}^n\IE[X_i^4]}}{2n}+\frac{2}{3n}\sum_{i=1}^n\IE\abs{X_i}^3.
    ```
  - Post-display i.i.d. rate remark (`L1091`):
    ```tex
    Note that if the $X_i$ are i.i.d. then this term is of order $n^{-1/2}$, which is best possible.
    ```
- **Issue (proof-step slip at `L1073-1074` and false remark at `L1091`; printed inequality `L1089` is TRUE for all $n \ge 1$)**:
  1. **Printed final inequality `L1089` is true for every $n \ge 1$**: Machine-checked unconditionally for all $n \ge 1$ in `Formalization/Leftovers/Ex36SmallN.lean` (`SteinMethod.indepSum_wassersteinDist_le_ex3_6_printed`, `Ex3_6_printed`) via a leave-one-out normal Stein kernel with exact rational SOS/Bernstein/Taylor certificates for $n \ge 2$ and a direct $1$-Lipschitz linear shift for $n = 1$.
  2. **Class C proof-step slip at `L1073-1074`**: Because $W' - W = (X_I' - X_I)/\sqrt{n}$ with $I$ uniform on $\{1, \ldots, n\}$ independent of $(X_i, X_i')$, averaging over $I$ contributes an extra factor $\frac{1}{n}$, giving
     $$\mathbb{E}|W' - W|^3 = \frac{1}{n}\sum_{i=1}^n \mathbb{E}\left|\frac{X_i' - X_i}{\sqrt{n}}\right|^3 = \frac{1}{n^{5/2}}\sum_{i=1}^n \mathbb{E}|X_i - X_i'|^3 \le \frac{8}{n^{5/2}}\sum_{i=1}^n \mathbb{E}|X_i|^3.$$
     `L1073-1074` omits this $\frac{1}{n}$ factor. Substituting the corrected third-moment bound into $\frac{\mathbb{E}|W' - W|^3}{3a}$ in Theorem 3.7 (`\label{thm51}`, $a = 1/n$) yields the sharper $O(n^{-1/2})$ second term $\frac{8}{3 n^{3/2}}\sum_{i=1}^n \mathbb{E}|X_i|^3$ (`Ex3_6_corrected`), which directly implies `L1089` for $n \ge 16$ (`Ex3_6_restricted`).
  3. **False i.i.d. $O(n^{-1/2})$ rate remark at `L1091`**: For i.i.d. $X_i$ with $\mathbb{E}[X_1] = 0$, $\mathrm{Var}(X_1) = 1$, and $X_1 \in L^4(P)$, the printed second term at `L1089` equals
     $$\frac{2}{3n}\sum_{i=1}^n \mathbb{E}|X_i|^3 = \frac{2}{3}\mathbb{E}|X_1|^3 \ge \frac{2}{3}(\mathbb{E}[X_1^2])^{3/2} = \frac{2}{3},$$
     which is independent of $n$ and does **not** decay as $O(n^{-1/2})$ (the $O(n^{-1/2})$ remark holds only for the corrected $\frac{8}{3 n^{3/2}}$ bound). Machine-checked in `Formalization/Leftovers/Ex36SmallN.lean` as `SteinMethod.ex3_6_printed_second_term_ge_two_thirds` and `SteinMethod.ex3_6_printed_iid_not_bigO_inv_sqrt`.
- **Resolution**: Formalize `Ex3_6_printed` (the printed `L1089` bound for all $n \ge 1$, without auxiliary coupling variables) alongside `Ex3_6_corrected` (`8 / (3 * n^{3/2})` for all $n \ge 1$ via the Stein pair) and `Ex3_6_restricted` (`n ≥ 16` corollary of `Ex3_6_corrected`), and refute the `L1091` i.i.d. rate remark via `ex3_6_printed_iid_not_bigO_inv_sqrt`.

---

### `ISSUE-3.8` — Anti-Voter Chain Fails Irreducibility on $\{-1, 1\}^V$ and Fails Stationary Uniqueness Without Connectedness (`L1101-1111`)
- **Source**: Section 3.3.1 prose preceding Theorem 3.8 (`SteinIntro.tex:1101-1111`)
- **Printed text (verbatim, `L1101-1111`)**:
  ```tex
  Let $G$ be an $r$-regular\footnote{The term $r$-regular means that every vertex has degree $r$.}
  graph with vertex set $V$ and edge set $E$.  Define
  a Markov chain on the space $\{-1, 1\}^V$ of labelings of the vertices of $V$ by $+1$ and $-1$.  The chain follows the rule of uniformly 
  choosing a vertex $v\in V$, then uniformly choosing a neighbor of $v$ and changing the sign of the label of $v$ to the opposite of
  its neighbor.  The model gets its name from thinking of the vertices as people in a town full of curmudgeons where
  a positive (negative)
  labeling corresponding to a yes (no) vote for some measure.  At each time unit a random person talks to a random neighbor
  and decides to switch votes to the opposite of that neighbor.  

  It is known \cite{af10} that if the underlying graph $G$ is not bipartite or a cycle, then the anti-voter chain is irreducible and aperiodic
  and has a unique stationary distribution.
  ```
- **Issue 1 — Irreducibility Fails on Full State Space $\{-1, 1\}^V$**:
  - On any nonempty graph $G$ without isolated vertices (in particular, any $r$-regular graph that is not bipartite, where $r \ge 1$ and $|V| \ge 3$), one step of the anti-voter chain selects $v \in V$ and $u \in N_G(v)$ ($u \ne v$) and returns $y = x[v \mapsto -x_u]$, which attains both $+1$ (at $u$ or $v$) and $-1$ (at $v$ or $u$).
  - Hence the two constant labelings $(+1)^V$ and $(-1)^V$ have **zero** incoming transition probability from every state $x \in \{-1, 1\}^V$: they are transient and unreachable in $\ge 1$ steps, refuting irreducibility on $\{-1, 1\}^V$ (`SteinMethod.antiVoterStep_support_nonconst` and `SteinMethod.antiVoterStep_const_eq_zero` in `Formalization/Exchangeable/AntiVoterGraph.lean`). Irreducibility and aperiodicity hold only on the absorbing set $\mathcal{N}(V)$ of non-constant labelings.
- **Issue 2 — Omitted `G.Connected` Hypothesis Refutes Stationary Uniqueness (`K_3 ⊔ C_4` on `Fin 7`)**:
  - `L1101-1111` omits the hypothesis that $G$ is **connected** (assumed throughout Aldous–Fill `[af10]`, Chapter 14). Because constant labelings are transient, stationary uniqueness on $\{-1, 1\}^V$ is identical to stationary uniqueness on $\mathcal{N}(V)$.
  - For disconnected $G$ without isolated vertices, irreducibility on $\mathcal{N}(V)$ always fails, and **stationary uniqueness fails if and only if at least one connected component of $G$ is bipartite** (a bipartite component admits two frozen proper $2$-colorings; if no component is bipartite, e.g. $K_3 \sqcup K_3$, $K_4 \sqcup K_4$, or $C_5 \sqcup K_3$, the stationary distribution remains unique despite reducibility on $\mathcal{N}(V)$).
  - **Concrete counterexample refuting the printed uniqueness claim ($G = K_3 \sqcup C_4$ on `Fin 7`)**: Let $\{0, 1, 2\}$ form $K_3$ and $\{3, 4, 5, 6\}$ form the $4$-cycle $3 \sim 4 \sim 5 \sim 6 \sim 3$. Then $G$ is $2$-regular, not bipartite (contains $K_3$), and not isomorphic to `cycleGraph 7`. Pairing the uniform measure on the $6$ non-constant labelings of $K_3$ with each of the two frozen proper $2$-colorings $(+1, -1, +1, -1)$ and $(-1, +1, -1, +1)$ of $C_4$ yields two closed classes of $6$ states each and two distinct, mutually singular stationary probability measures $\nu_1 \ne \nu_2$ on $\{-1, 1\}^V$. Machine-checked as `SteinMethod.antiVoter_disconnected_counterexample` (`Formalization/Exchangeable/AntiVoterUnique.lean`) and `SteinMethod.not_Sec3_3_1_antiVoter_unique_printed` (`Formalization/Statements/Sec3Proofs.lean`).
- **Resolution & Scope Note**:
  1. `Sec3_3_1_antiVoter_ergodic_corrected` (`Formalization/Statements/Sec3.lean`) adds `G.Connected`, states one-step absorption + irreducibility/aperiodicity on $\mathcal{N}(V)$, and proves existence, full support on $\mathcal{N}(V)$, and uniqueness of the stationary probability distribution on `V → Bool` from scratch (`SteinMethod.antiVoter_irreducible_on_nonconst` in `AntiVoterIrreducible.lean` and `SteinMethod.antiVoter_ergodic_and_unique_stationary` in `AntiVoterUnique.lean`, where $r$-regularity is also dropped).
  2. `not_Sec3_3_1_antiVoter_unique_printed` machine-checks the failure of the printed stationary-uniqueness claim without `G.Connected`.
  3. `Thm3_8` and `Lem3_10` quantify universally over every stationary distribution `ν` (`IsAntiVoterStationary G (P.map X)`) and rely only on `1 ≤ kappa G`, which holds without connectedness; thus `Thm3_8` and `Lem3_10` require no modification.

---

### `ISSUE-3.10` — Zero-Bias Non-Existence When $\mathbb{E}|W|^3 = \infty$ (Critic Finding H4 Verified)
- **Source**: Definition 3.10 (`SteinIntro.tex:1442-1449`) and Proposition 3.19(1) (`\label{i81}`, `SteinIntro.tex:1471-1485`)
- **Printed text**:
  - Definition 3.10 (`L1443-1448`): *"For a random variable $W$ with $\mathbb{E}[W] = 0$ and $\mathrm{Var}(W) = \sigma^2 < \infty$, we say the random variable $W^z$ has the zero-bias distribution with respect to $W$ if for all absolutely continuous $f$ such that $\mathbb{E}|W f(W)| < \infty$ we have $\mathbb{E}[W f(W)] = \sigma^2 \mathbb{E}[f'(W^z)]$."*
  - Proposition 3.19(1) (`L1474-1478`): *"There is a unique probability distribution for a random variable $W^z$ satisfying $\mathbb{E}[W f(W)] = \sigma^2 \mathbb{E}[f'(W^z)]$ for all absolutely continuous $f$ such that $\mathbb{E}|W f(W)| < \infty$."*
- **Written Verification of H4 (Explicit Counterexample)**:
  1. Let $W$ have the symmetric probability density on $\mathbb{R}$ given by
     $$p_W(w) := \frac{3}{2}|w|^{-4}\,\mathbf{1}_{|w| \ge 1}.$$
     Then $\int_{\mathbb{R}} p_W(w)\,dw = 3\int_1^\infty w^{-4}\,dw = 1$, $\mathbb{E}|W| = 3\int_1^\infty w^{-3}\,dw = \frac{3}{2} < \infty$, $\mathbb{E}[W] = 0$ by symmetry, and $\sigma^2 = \mathrm{Var}(W) = 3\int_1^\infty w^{-2}\,dw = 3 < \infty$ (while $\mathbb{E}|W|^3 = \infty$).
  2. Suppose a probability measure $\nu$ on $\mathbb{R}$ satisfies $\mathbb{E}[W g(W)] = 3 \int_{\mathbb{R}} g'(u)\,d\nu(u)$ for every $g \in C_c^1(\mathbb{R})$ (all of which are locally AC and bounded, so $\mathbb{E}|W g(W)| \le \|g\|_\infty \mathbb{E}|W| < \infty$). By integration by parts on $C_c^1(\mathbb{R})$, $\nu$ is uniquely forced to be the absolutely continuous measure with density `(3.32)` (`L1481-1483`):
     $$p^z(u) = \frac{1}{3}\mathbb{E}[W \mathbf{1}_{W > u}] = \begin{cases} \dfrac{1}{4} & \text{if } |u| \le 1, \\[6pt] \dfrac{1}{4 u^2} & \text{if } |u| > 1. \end{cases}$$
  3. Now consider the function
     $$f(w) := \bigl(1 - \cos(w^2 - 1)\bigr)\mathbf{1}_{w > 1}, \qquad f'(w) = 2 w \sin(w^2 - 1)\mathbf{1}_{w > 1}.$$
     Because $f(1) = 0$ and $\lim_{w \downarrow 1} 2 w \sin(w^2 - 1) = 0$, $f \in C^1(\mathbb{R})$, hence $f$ is locally absolutely continuous (`∀ a b, AbsolutelyContinuousOnInterval f a b`). Moreover, $0 \le f(w) \le 2$ everywhere and $f(w) > 0$ a.e. on $(1, \infty)$, so
     $$\mathbb{E}|W f(W)| = \frac{3}{2}\int_1^\infty \frac{1 - \cos(w^2 - 1)}{w^3}\,dw \le 3\int_1^\infty w^{-3}\,dw = \frac{3}{2} < \infty,$$
     and strictly $\mathbb{E}[W f(W)] = \frac{3}{4}\int_0^\infty \frac{1 - \cos v}{(v + 1)^2}\,dv > 0$.
  4. However, under the unique candidate law $\nu$, substituting $v = u^2 - 1$ gives
     $$\int_{\mathbb{R}} |f'(u)|\,p^z(u)\,du = \int_1^\infty 2 u |\sin(u^2 - 1)| \cdot \frac{1}{4 u^2}\,du = \frac{1}{4}\int_0^\infty \frac{|\sin v|}{v + 1}\,dv \ge \frac{1}{2}\sum_{k=0}^\infty \frac{1}{(k + 1)\pi + 1} = +\infty.$$
     Thus $\mathbb{E}[f'(W^z)]$ fails to exist in the Lebesgue sense (refuting existence in Proposition 3.19(1) classically), and under Lean's Bochner integral convention `∫ u, deriv f u ∂ν = 0`, giving $3 \cdot 0 = 0 \ne \mathbb{E}[W f(W)] > 0$ (refuting Proposition 3.19(1) in Lean as well).
- **Resolution (`D9`)**: `H4` is **confirmed**. `SteinMethod.IsZeroBias` quantifies over locally AC `f` for which both `Integrable (fun ω ↦ W ω * f (W ω)) P` and `Integrable (fun ω' ↦ deriv f (Wz ω')) P'` hold, and Proposition 3.19 is formalized as `Prop3_19_corrected` (incorporating `0 < σ²` from `ISSUE-3.19`).

---

### `ISSUE-3.11` — Division by $\mu = 0$ in Proposition 3.11 and Corollary 3.12
- **Source**: Proposition 3.11 (`SteinIntro.tex:1239-1245`) and Corollary 3.12 (`SteinIntro.tex:1246-1252`)
- **Printed text**: *"If $X \ge 0$ is a random variable with $\mathbb{E}[X] = \mu < \infty$ and distribution function $F$, then the size-bias distribution of $X$ is absolutely continuous with respect to the measure of $X$ with density read from $dF^s(x) = \frac{x}{\mu} dF(x)$."*
- **Counterexample**: Let $X \equiv 0$, so $X \ge 0$, $\mu = \mathbb{E}[X] = 0 < \infty$, and $\mathrm{Law}(X) = \delta_0$. By Definition 3.7 (`IsSizeBias`), $\mathbb{E}[X f(X)] = 0 = 0 \cdot \mathbb{E}[f(X^s)]$ holds for **every** random variable $X^s$: e.g. $X^s \equiv 1$ satisfies Definition 3.7, yet $\delta_1$ is **not** absolutely continuous with respect to $\delta_0$, and in Lean `x / 0 = 0` makes `(P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / 0)) = 0`, which is not a probability measure.
- **Resolution (`D8`)**: Keep $\mu = 0$ allowed in `IsSizeBias`, and formalize `Prop3_11_restricted` and `Cor3_12_restricted` with the hypothesis `0 < ∫ ω, X ω ∂P`.

---

### `ISSUE-3.9` — Algebra Errors in $\mathbb{E}[Y_1 Y_2]$ (`L1397`) and $\mathrm{Var}(\sum_{i=1}^n D_i)$ (`L1395`), Plus Crude $+1$ Bound at `L1403-1404`, in Example 3.9
- **Source**: Example 3.9 (`\label{ex72}`, `SteinIntro.tex:1390-1405`, and asymptotic proof step at `L1424`)
- **Printed text (verbatim, `L1393-1405`)**:
  - `L1393-1397`:
    ```tex
    &\var\left(\sum_{i=1}^nD_i\right)=n(n-1)p(1-p)^{n-2}\left(1-(n-1)p(1-p)^{n-2}\right)+n(n-1)\cov(Y_1, Y_2) \\
    	&=n(n-1)p(1-p)^{n-2}\left[1-(n-1)p(1-p)^{n-2}+(1-p)^{n-2}+(n-1)^2p^2(1-p)^{n-3}\right],
    ```
    *"since $\mathbb{E}[Y_1 Y_2]=p(1-p)^{2n-4}+(n-1)^2p^2(1-p)^{2n-5}$ (the first term corresponds to $v_1$ and $v_2$ being joined)."*
  - `L1401-1405`:
    ```tex
    \IE[(X^s-X)^2]&=\IE\left[\IE[(X^s-X)^2|X]\right] \\
    	&=\frac{1}{n}\sum_{i=1}^n\IE[(D_i+\I[d_i>0])^2] \\
    	&\leq \frac{1}{n}\sum_{i=1}^n\IE[(D_i+1)^2] \\
    	&=\IE[D_1^2]+2\IE[D_1]+1.
    ```
- **Independent Verification & Concrete Small-$n$ Counterexample ($n = 3, p = 1/2$)**:
  1. **True formulas in Example 3.9**: $\mu = n(1-p)^{n-1}$ (`L1372`), $\mathbb{E}[X_1 X_2] = (1-p)^{2n-3}$ (`L1379`, $n \ge 2$), $\sigma^2 = \mu[1 + (np - 1)(1-p)^{n-2}]$ (`L1377`, eq. `\label{77}`, $n \ge 2$), $X^s - X = D_I + \mathbb{I}[d_I > 0]$ (`L1382`), the first line of `L1394` (`Var(∑ D_i) = n Var(Y_1) + n(n-1) Cov(Y_1, Y_2)`), and $\mathbb{E}[D_1^2] = (n-1)p(1-p)^{n-2} + (n-1)(n-2)p^2(1-p)^{2n-5}$ (`L1408`, $n \ge 3$) are all **exact**.
  2. **False formula 1 (`L1397`, $\mathbb{E}[Y_1 Y_2]$)**: Here $Y_i = \mathbb{I}[d_i = 1]$. When $v_1$ and $v_2$ are not joined (factor $1 - p$), each of $v_1$ and $v_2$ must have a unique neighbor chosen from the remaining **$n - 2$** vertices $\{v_3, \ldots, v_n\}$ ($(n-2)^2$ ordered choices, with edge status on the $2(n-2)$ edges between $\{v_1, v_2\}$ and $\{v_3, \ldots, v_n\}$ having probability $p^2 (1-p)^{2n-6}$), giving
     $$\mathbb{E}[Y_1 Y_2] = p(1-p)^{2n-4} + (n-2)^2 p^2 (1-p)^{2n-5}$$
     for $n \ge 3$, whereas `L1397` prints $(n-1)^2$ in place of $(n-2)^2$.
     - *Check at $n = 3, p = 1/2$* ($8$ equally likely graphs on $\{v_1, v_2, v_3\}$): $Y_1 Y_2 = 1$ iff both $v_1$ and $v_2$ have degree $1$, which occurs on exactly $2$ of the $8$ graphs (the single-edge graph $\{v_1 v_2\}$, and the $2$-edge path $\{v_1 v_3, v_2 v_3\}$), so $\mathbb{E}[Y_1 Y_2] = \frac{2}{8} = \frac{1}{4}$ (matching $\frac{1}{2}(\frac{1}{2})^2 + 1^2(\frac{1}{2})^2(\frac{1}{2})^1 = \frac{1}{8} + \frac{1}{8} = \frac{1}{4}$), whereas printed `L1397` gives $\frac{1}{8} + 2^2 \cdot \frac{1}{4} \cdot \frac{1}{2} = \frac{5}{8} \ne \frac{1}{4}$.
  3. **False formula 2 (`L1395`, $\mathrm{Var}(\sum_{i=1}^n D_i)$)**: Beyond inheriting $(n-1)^2$ from `L1397`, `L1395` commits two additional algebra errors when factoring $n(n-1)p(1-p)^{n-2}$ out of $n(n-1)\mathrm{Cov}(Y_1, Y_2) = n(n-1)(\mathbb{E}[Y_1 Y_2] - (n-1)^2 p^2 (1-p)^{2n-4})$: it writes $p^2$ instead of $p$ in the fourth bracketed term (failing to divide $p^2$ by the factored-out $p$), and it drops the $-(\mathbb{E}[Y_1])^2$ contribution from $\mathrm{Cov}(Y_1, Y_2)$ entirely. The true formula ($n \ge 3$) is
     $$\mathrm{Var}\!\left(\sum_{i=1}^n D_i\right) = n(n-1)p(1-p)^{n-2}\bigl[1 + (1-p)^{n-2} + (n-2)^2 p (1-p)^{n-3} - n(n-1)p(1-p)^{n-2}\bigr].$$
     - *Check at $n = 3, p = 1/2$*: $\sum_{i=1}^3 D_i = Y_1 + Y_2 + Y_3$ equals $0$ on the $0$-edge and $3$-edge graphs (probability $2/8 = 1/4$) and equals $2$ on the three $1$-edge and three $2$-edge graphs (probability $6/8 = 3/4$), so $\mathrm{Var}(\sum_{i=1}^3 D_i) = 4 \cdot \frac{3}{4} \cdot \frac{1}{4} = \frac{3}{4}$ (matching $\frac{3}{2}[1 + \frac{1}{2} + \frac{1}{2} - \frac{3}{2}] = \frac{3}{4}$), whereas printed `L1395` evaluates to $6 \cdot \frac{1}{2} \cdot \frac{1}{2}[1 - \frac{1}{2} + \frac{1}{2} + 4 \cdot \frac{1}{4} \cdot 1] = 3 \ne \frac{3}{4}$.
     - Both counterexamples at $n = 3, p = 1/2$ are machine-checked in `Formalization/RandomGraph/IsolatedMoments.lean` (`Ex3_9_L1397_counterexample`, `Ex3_9_L1395_counterexample`).
  4. **Proof note on `L1403-1404` vs `L1424`**: At `L1403-1404`, bounding $\mathbb{I}[d_i > 0] \le 1$ gives $\mathbb{E}[(X^s - X)^2] \le \mathbb{E}[D_1^2] + 2\mathbb{E}[D_1] + 1$, whose $+1$ term is $\Theta(1)$ and would not give the true rate $\mathbb{E}[(X^s - X)^2] \asymp n^{1-\alpha}$ claimed at `L1424` when $1 < \alpha < 2$ (where $\mu/\sigma^3 \asymp n / n^{3(1-\alpha/2)} = n^{3\alpha/2 - 2}$ exceeds $\sigma^{-1} \asymp n^{\alpha/2 - 1}$ by a factor of $n^{\alpha - 1}$). Because $D_i > 0 \implies d_i > 0$, $(D_i + \mathbb{I}[d_i > 0])^2 = D_i^2 + 2 D_i + \mathbb{I}[d_i > 0]$ holds **exactly**, giving $\mathbb{E}[(X^s - X)^2] = \mathbb{E}[D_1^2] + 2\mathbb{E}[D_1] + (1 - (1-p)^{n-1}) = \Theta(n p) = \Theta(n^{1-\alpha})$, so **Theorem 3.17 (`L1413-1420`) holds literally as printed**.
- **Resolution**: Formalize all verified formulas of Example 3.9 (`Ex3_9_moments` and `Ex3_9_sizeBias`), omit the false displays `L1395` and `L1397` (proving the exact formula for $\mathbb{E}[Y_1 Y_2]$ and the variance upper bound needed in `Formalization/RandomGraph/IsolatedMoments.lean`, plus machine-checked refutations of `L1395` and `L1397` at $n = 3, p = 1/2$), and prove `Thm3_17` literally under the asymptotic reading (`∀ᶠ n in Filter.atTop`).

---

### `ISSUE-3.19` — Non-Uniqueness and Division by $\sigma^2 = 0$ in Proposition 3.19 (and Section 3.6.1 Boundedness Parenthetical)
- **Source**: Proposition 3.19 (`SteinIntro.tex:1471-1485`, items `\label{i81}` and `\label{i82}`) and Section 3.6.1 prose parenthetical (`SteinIntro.tex:1741-1742`, `"note that $W$ bounded implies $W^z$ bounded"`)
- **Printed text**: For $W$ with $\mathbb{E}[W] = 0$ and $\mathrm{Var}(W) = \sigma^2 < \infty$, asserts uniqueness of $\mathrm{Law}(W^z)$ and absolute continuity with respect to Lebesgue measure with density $p^z(w) = \sigma^{-2}\mathbb{E}[W \mathbb{I}[W > w]]$; at `L1741-1742`, asserts parenthetically `"note that $W$ bounded implies $W^z$ bounded"`.
- **Counterexample**: Take $W \equiv 0$, so $\mathbb{E}[W] = 0$, $\sigma^2 = 0 < \infty$, and $|W| \le 0$ almost surely. Then $\mathbb{E}[W f(W)] = 0 = 0 \cdot \mathbb{E}[f'(W^z)]$ holds for **every** distribution of $W^z$ (e.g. $W^z \equiv 0$, $W^z \equiv 1$, and $W^z \sim \mathcal{N}(0, 1)$, violating uniqueness, Lebesgue absolute continuity for $\delta_0$, and all-versions boundedness for $\mathcal{N}(0, 1)$, machine-checked as `zero_stdNormalLaw_isZeroBias_unbounded` in `Formalization/Kolmogorov/ZeroBiasBound.lean`), and $\sigma^{-2} \mathbb{E}[W \mathbb{I}[W > w]] = 0$ integrates to $0 \ne 1$.
- **Resolution (`D9`)**: Formalize `Prop3_19_corrected` with `0 < ProbabilityTheory.variance W P` and the dual-integrability zero-bias predicate `IsZeroBias` (`ISSUE-3.10`), and formalize `Sec3_6_zeroBias_bdd_restricted` (`Formalization/Kolmogorov/ZeroBiasBound.lean`) for all zero-bias versions under `0 < ProbabilityTheory.variance W P` (together with `Sec3_6_zeroBias_bdd_exists` / `exists_bdd_zeroBias_of_pos_var_exists` for the existence reading taking $\nu = \delta_0$ at $\sigma^2 = 0$).
---

### `ISSUE-3.20` — Scaling Instance $\mathrm{Var}(aW) = a^2\sigma^2 = 0$ of `ISSUE-3.19` in Proposition 3.20 (`SteinIntro.tex:1519-1521`)
- **Printed text (verbatim, `L1519-1521`)**:
  ```tex
  \begin{proposition}
  If $W$ has mean zero and finite variance then $(aW)^z\ed~aW^z$.
  \end{proposition}
  ```
- **Two readings (`stmts-review-05A.md` `A3`)**:
  1. *Existence reading (`Prop3_20`)*: if $W^z$ has the zero-bias distribution of $W$, then $a W^z$ has the zero-bias distribution of $a W$ for **every** $a \in \mathbb{R}$ with no variance positivity requirement (`IsZeroBias.const_mul`).
  2. *Law-identity reading (`Prop3_20_restricted`)*: distributional uniqueness $(a W)^z \stackrel{d}{=} a W^z$ across arbitrary zero-bias realizations of $a W$ is an instance of `ISSUE-3.19` requiring $\mathrm{Var}(a W) = a^2 \sigma^2 > 0$, i.e., $\sigma^2 > 0$ and $a \ne 0$. Even when $\sigma^2 = 1 > 0$ ($W \sim \mathcal{N}(0, 1)$), at $a = 0$ we have $\mathrm{Var}(0 \cdot W) = 0$, so $Y \equiv 1$ satisfies `IsZeroBias` for $0 \cdot W$ while $0 \cdot W^z \equiv 0$ (machine-checked as `not_Prop3_20_printed` in `Formalization/ZeroBias/Density.lean`).

---

### `ISSUE-3.5.2-PROSE` — `"not sufficient"` Slip for `"not necessary"` After Display `(3.34)` (`L1565-1566`)
- **Source**: Unnumbered prose immediately following display `(3.34)` (`\label{85}`, `SteinIntro.tex:1565-1566`)
- **Printed text (verbatim, `L1565-1566`)**:
  ```tex
  The condition ensures that no single term dominates in the sum so that the limit is not altered by the distribution of a summand.  Note that
  the condition is not sufficient as we could take $X_{1,n}$ to be standard normal and the rest of the terms zero.
  ```
- **Slip & Counterexample Verification**: Immediately after introducing `(3.34)` at `L1560-1564` as *"A sufficient condition for $W_n$ to satisfy a CLT as $n\rightarrow\infty$ is the Lindeberg condition"* (proved for centered arrays as `Sec3_5_2_lindeberg_sufficient`), `"not sufficient"` at `L1566` is a slip of the pen for **"not necessary"**: taking $X_{1,n} \sim \mathcal{N}(0, 1)$ and $X_{i,n} = 0$ for $i > 1$ gives $W_n \sim \mathcal{N}(0, 1) \xrightarrow{d} \mathcal{N}(0, 1)$ while violating `(3.34)` because $\mathbb{E}[X_{1,n}^2 \mathbb{I}[|X_{1,n}| > 1]] > 0$ is constant in $n$.
- **Resolution**: Formalize `Sec3_5_2_lindeberg_not_necessary_corrected` (`lindeberg_not_necessary_for_clt` in `Formalization/ZeroBias/LindebergFeller.lean`).

---

### `ISSUE-4.7` — Omitted $i \in N_i$ Hypothesis in Theorem 4.7
- **Source**: Theorem 4.7 (`\label{thm103}`, `SteinIntro.tex:1970-1977`; Remark 4.1 `L1978-1981`; proof at `SteinIntro.tex:1982-2000`)
- **Printed text (verbatim, `L1971-1976`)**:
  *"Let $X_1, \ldots, X_n$ indicator variables with $\mathbb{P}(X_i=1)=p_i$, $W=\sum_{i=1}^n X_i$, and $\lambda=\mathbb{E}[W]=\sum_i p_i$. For each $i$, let $N_i\subseteq\{1, \ldots, n\}$ such that $X_i$ is independent of $\{X_j: j\not\in N_i\}$. If $p_{i j}:=\mathbb{E}[X_i X_j]$ and $Z\sim\mathrm{Po}(\lambda)$, then*
  $$d_{\mathrm{TV}}(W,Z)\leq \min\{1, \lambda^{-1}\}\left(\sum_{i=1}^n\sum_{j\in N_i} p_i p_j +\sum_{i=1}^n\sum_{j\in N_i/\{i\}} p_{i j}\right).\text{''}$$
- **Counterexample**: Let $n = 1$, $X_1 \equiv 1$ ($p_1 = 1$, $\lambda = 1$), and $N_1 = \emptyset$. Because a constant random variable is independent of every family of random variables (including $\{X_1\}$ itself), $X_1$ is independent of $\{X_j : j \notin \emptyset\} = \{X_1\}$. Yet both inner sums over $j \in N_1 = \emptyset$ and $j \in N_1 / \{1\} = \emptyset$ vanish, giving right-hand side $0$, whereas $d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1)) = 1 - e^{-1} > 0$.
- **Resolution**: Formalize `Thm4_7_corrected` adding `∀ i, i ∈ N i`, because the proof at `SteinIntro.tex:1984-1996` sets $W_i = W - X_i$ and $V_i = \sum_{j \notin N_i} X_j$ (`L1984`) and bounds $|W_i - V_i| \le \sum_{j \in N_i / \{i\}} X_j$ (`L1996`), which requires $i \in N_i$ so $X_i$ is absent from $V_i$ (with machine-checked refutation `not_Thm4_7_printed` in `Formalization/PoissonDep/LocalDependence.lean`).

---

### `ISSUE-4.9` — Omitted Rare-Event Regime $0 < p < a \le 1$ in Erdős–Rényi Law (Theorem 4.9)
- **Source**: Section 4.2.1 prose and Theorem 4.9 (`[\ER\ Law]`, `SteinIntro.tex:2066-2078`)
- **Printed text (verbatim, `L2066-2078`)**:
  ```tex
  For example, for $0< a \leq 1$, we can define a ``quality $a$" run of length $j$ to be a run of length $j$ with at least $aj$ heads.  We could then
  take $W$ to be the number of quality $a$ runs of length at least $k$ and $R_n$ to be the longest quality $a$ run in $n$ independent coin tosses.
  A story analogous to that above emerges.  

  These particular results can also be viewed as elaborations of the classical theorem:
  \begin{theorem}[\ER\ Law]
  If $R_n$ is the longest quality $a$ head run in a sequence of $n$ independent tosses
  of a coin with head probability $p$ as defined above, then almost surely,
  \ba
  \frac{R_n}{\log(n)}\to \frac{1}{H(a, p)},
  \ee
  where for $0< a< 1$, $H(a, p)=a\log(a/p)+(1-a)\log((1-a)/(1-p))$, and $H(1, p)=\log(1/p)$.
  \end{theorem}
  ```
- **Counterexample (`not_Thm4_9_printed`)**: When $0 < a < p < 1$, $H(a, p)$ is strictly positive and finite, yet the printed limit is false. Take i.i.d. $Y_i \sim \mathrm{Bernoulli}(1/2)$ ($p = 1/2$) and $a = 1/4 \in (0, 1)$:
  - $H(1/4, 1/2) = \frac{3}{4} \log 3 - \log 2 \approx 0.130812 > 0$, so $1 / H(1/4, 1/2) \approx 7.6445$ is finite;
  - by the fourth-moment Markov bound $\mathbb{P}(\sum_{i=1}^n Y_i < n / 4) \le 48 / n^2$ and the first Borel–Cantelli lemma, almost surely $R_n = n$ for all sufficiently large $n$, so $R_n / \log(n) = n / \log(n) \to +\infty \ne 1 / H(1/4, 1/2)$.
  - In addition, $H(p, p) = 0$ divides by zero at $a = p$ (including $a = p = 1$), $\log(a / 0)$ divides by zero at $p = 0$, and almost-sure convergence as $n \to \infty$ requires $R_n$ to be formed from prefixes of a single infinite sequence $(Y_i)_{i \ge 0}$. In Erdős & Rényi (1970, Theorem 2) and Arratia–Gordon–Waterman (`[agw90]`), the hypothesis is $0 < p < a \le 1$.
- **Resolution**: Formalize `Thm4_9_corrected` (`erdos_renyi_longestQualityRun_ae` in `Formalization/PoissonDep/ErdosRenyiLaw.lean`) under `0 < p`, `p < a`, `a ≤ 1` on prefixes of `Y : ℕ → Ω → ℕ`, and prove `not_Thm4_9_printed` in `Formalization/PoissonDep/ErdosRenyiCounterexample.lean`.

---

### `ISSUE-4.17` — Two-Reading Direction Ambiguity in Monotone-Indicator Theorem 4.17
- **Source**: Definition 4.9 (`SteinIntro.tex:2377-2381`) and Theorem 4.17 (`\label{thm124}`, `SteinIntro.tex:2382-2390`)
- **Printed text (verbatim)**:
  - Definition 4.9 (`L2378-2380`): *"We say a function $f:\mathbb{R}^n\to\mathbb{R}$ is increasing (decreasing) if for all $\textbf{x}=(x_1, \ldots, x_n)$ and $\textbf{y}=(y_1, \ldots, y_n)$ such that $x_i\leq y_i$ for all $i= 1, \ldots, n$, we have $f(\textbf{x})\leq f(\textbf{y})$ ($f(\textbf{x})\geq f(\textbf{y})$)."*
  - Theorem 4.17 (`L2383-2389`): *"Let $\textbf{Y}=(Y_i)_{j=1}^N$ be a finite collection of independent indicators and assume $X_1, \ldots, X_n$ are increasing or decreasing functions from $\{0,1\}^N$ into $\{0, 1\}$. If $W=\sum_{i=1}^n X_i(\textbf{Y})$ and $\mathbb{E}[W]=\lambda$, then*
    $$d_{\mathrm{TV}}(W, Z) \leq \min\{1, \lambda^{-1}\}\left(\mathrm{Var}(W)-\lambda+2\sum_{i=1}^n p_i^2\right).\text{''}$$
- **Two-reading ambiguity & counterexample to Reading (A)**:
  The phrasing *"assume $X_1, \ldots, X_n$ are increasing or decreasing functions from $\{0, 1\}^N$ into $\{0, 1\}$"* (`L2383-2384`, echoed on `L2395`) admits two readings:
  - **Reading (A)** (individual direction): for each $i$, $X_i$ is increasing or $X_i$ is decreasing, possibly in opposite directions for different indices $i$.
  - **Reading (B)** (common direction): all $X_1, \ldots, X_n$ are increasing, or all $X_1, \ldots, X_n$ are decreasing.
  Reading (A) is **false**: take $N = 1$, $Y_1 \sim \mathrm{Bernoulli}(1/2)$, $n = 2$, $X_1(y_1) = y_1$ (increasing), and $X_2(y_1) = 1 - y_1$ (decreasing). Then $W = X_1(Y_1) + X_2(Y_1) \equiv 1$, $\lambda = 1$, $\mathrm{Var}(W) = 0$, and $p_1 = p_2 = 1/2$, so the printed upper bound is $\min\{1, 1\}(0 - 1 + 2(1/4 + 1/4)) = 0$, whereas $d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1)) = 1 - e^{-1} > 0$. (The FKG step at `L2395-2401` requires $\phi \circ \mathbf{X}$ to be monotone in the same direction as $X_i$.)
- **Resolution**: Formalize `Thm4_17_corrected` under Reading (B) (all $X_1, \ldots, X_n$ increasing, or all $X_1, \ldots, X_n$ decreasing).

---

### `ISSUE-5.7` — Unstated Support $M \ge 1$ and Joint Independence of $(N, M)$ from $(X_i)$ in Theorem 5.7
- **Source**: Theorem 5.7 (`\label{thm1710}`, `SteinIntro.tex:2915-2929`)
- **Printed text (verbatim, `L2916-2928`)**:
  *"Let $X_1, X_2, \ldots$ be square integrable, non-negative, and independent random variables with $\mathbb{E}[X_i]=1$. Let $N>0$ be an integer valued random variable with $\mathbb{E}[N]=1/p$ for some $0 \lt p\leq 1$ and let $M$ be defined on the same space as $N$ such that $\mathbb{P}(M=m)=p \mathbb{P}(N\geq m)$. If $W=p\sum_{i=1}^N X_i$, $Z\sim\mathrm{Exp}(1)$, and $X_i^e$ is an equilibrium coupling of $X_i$ independent of $N, M$, and $(X_j)_{j\not=i}$, then $d_{\mathrm{W}}(W, Z)\leq 2p\left(\mathbb{E}|X_M-X_M^e|+\mathbb{E}|N-M|\right) \leq 2p\left(1+\frac{\mu_2}{2}+\mathbb{E}|N-M|\right)$, where $\mu_2:=\sup_{i} \mathbb{E}[X_i^2]$."*
- **Issues & Counterexamples**:
  1. *Omitted $m \ge 1$ restriction in `L2920`*: Because $N > 0$ is integer-valued with $\mathbb{E}[N] = 1/p$, $\sum_{m=1}^\infty p \mathbb{P}(N \ge m) = p \mathbb{E}[N] = 1$. However, `L2920` prints $\mathbb{P}(M = m) = p \mathbb{P}(N \ge m)$ without restricting $m \ge 1$; for every integer $m \le 0$, $\mathbb{P}(N \ge m) = 1$, which would assign mass $p > 0$ to infinitely many $m \le 0$ (and $X_M$ at `L2925` is only indexed for $M \ge 1$). Thus $M$ must take values in $\{1, 2, \ldots\}$ with $\mathbb{P}(M = m) = p \mathbb{P}(N \ge m)$ for $m \ge 1$ (matching Remark 5.5 at `L2935`).
  2. *Omitted independence of $(N, M)$ from $(X_i)_{i \ge 1}$*: `L2916-2922` omits that $(N, M)$ is independent of $(X_i)_{i \ge 1}$ (unlike Theorem 5.6 at `L2906-2907`). Counterexample: let $X_i \stackrel{\text{i.i.d.}}{\sim} 2\,\mathrm{Bernoulli}(1/2)$ ($\mathbb{E}[X_i] = 1$, $\mu_2 = 2$), let $X_i^e \stackrel{\text{i.i.d.}}{\sim} \mathrm{Unif}(0, 2)$ completely independent of $(X_j)_{j \ge 1}$, fix a large odd integer $m$, set $p = 1 - 2^{-1/m}$ so $\mathbb{P}(G \le m) = 1/2$ for an independent $G \sim \mathrm{Geom}(p)$, and sample $N = M$ from $\mathrm{Law}(G \mid G > m)$ when $S_m := \sum_{i=1}^m (X_i - 1) > 0$ and from $\mathrm{Law}(G \mid G \le m)$ when $S_m < 0$. Then $N = M \sim \mathrm{Geom}(p)$ ($\mathbb{E}|N - M| = 0$) and every printed hypothesis holds, yet $d_{\mathrm{W}}(W, Z) \ge \mathbb{E}[W] - 1 = p\,\mathbb{E}[S_N] = \frac{p}{2}(1 - \frac{\mathbb{E}[G \mid G \le m]}{m})\mathbb{E}|S_m| = \Theta(\sqrt{p})$, which exceeds $2p(1 + \mu_2/2 + 0) = 4p$ for all sufficiently large odd $m$.
- **Resolution**: Formalize `Thm5_7_corrected` requiring $M \ge 1$ with $\mathbb{P}(M = m) = p \mathbb{P}(N \ge m)$ for $m \ge 1$ and joint independence of $(N, M)$ from $((X_i, X_i^e))_{i \ge 1}$ (see also [`docs/DEFINITIONS.md`](DEFINITIONS.md) §5.3 for the Lean real/extended-real encoding note).

---

### `ISSUE-5.9` — Boundary Case $n = 1$ ($\log 1 = 0$) and $\sigma^2 = 0$ in Theorem 5.9
- **Source**: Theorem 5.9 (`SteinIntro.tex:3015-3020`)
- **Printed text**: For a critical branching process $Z_n$ with $\mathrm{Var}(Z_1) = \sigma^2 < \infty$, $\mathbb{E}[Z_1^3] < \infty$, and $Y_n \stackrel{d}{=} Z_n \mid Z_n > 0$, asserts existence of $C > 0$ such that $d_{\mathrm{W}}(\frac{2 Y_n}{n \sigma^2}, Z) \le C \frac{\log(n)}{n}$ for $Z \sim \mathrm{Exp}(1)$.
- **Counterexample**: Take $\mathbb{P}(Z_1 = 0) = \mathbb{P}(Z_1 = 2) = 1/2$, so $\mathbb{E}[Z_1] = 1$, $\sigma^2 = 1 > 0$, and $\mathbb{E}[Z_1^3] = 4 < \infty$. At $n = 1$, $Y_1 \equiv 2$ deterministically, so $\frac{2 Y_1}{1 \cdot \sigma^2} \equiv 4$ and $d_{\mathrm{W}}(\delta_4, \mathrm{Exp}(1)) \ge |4 - 1| = 3 > 0$, whereas for **every** constant $C > 0$, $C \frac{\log(1)}{1} = 0$. (Also at $\sigma^2 = 0$, $Z_1 \equiv 1$ and $2 Y_n / (n \sigma^2)$ divides by zero.)
- **Resolution**: Formalize `Thm5_9_corrected` requiring `0 < σ²` and `2 ≤ n`.

---

### `ISSUE-6.0` — Omitted Scaling Factor $p$ on $d_{\mathrm{W}}(X, W)$ in Section 6 Opening Display
- **Source**: Section 6 opening paragraph (`SteinIntro.tex:3193-3198`)
- **Printed text (verbatim)**:
  ```tex
  Due to Example \ref{ex171}, if $W>0$ is integer-valued such that $W/\IE[W]$ is approximately exponential and $\IE[W]$ is large, then 
  we expect that $W$ will be approximately geometrically distributed.  In fact, if we write $\IE[W]=1/p$, and let $X\sim\Ge(p)$ and 
  $Z\sim\Exp(1)$, then the triangle inequality implies that
  \ba
  \left|\dw(pW, Z)-\dw(X, W)\right|\leq p.
  \ee
  ```
- **Counterexample (`not_Sec6_opening_wasserstein_printed`)**: Take $p = 1/4$ and $W \equiv 4$ deterministically ($W > 0$ integer-valued with $\mathbb{E}[W] = 4 = 1/p$). Then $p W \equiv 1$, $d_{\mathrm{W}}(\delta_1, \mathrm{Exp}(1)) = 2 e^{-1} < 1$, whereas $X \sim \mathrm{Ge}(1/4)$ on $\{1, 2, \dots\}$ satisfies $d_{\mathrm{W}}(X, 4) = \mathbb{E}|X - 4| = 2 \cdot \frac{81}{64} = \frac{81}{32}$, so $|d_{\mathrm{W}}(pW, Z) - d_{\mathrm{W}}(X, W)| = \frac{81}{32} - 2 e^{-1} \approx 1.80 > \frac{1}{4} = p$.
- **Cause & Resolution**: By homogeneity of Wasserstein distance, $d_{\mathrm{W}}(p X, p W) = p\,d_{\mathrm{W}}(X, W)$, so the reverse triangle inequality combined with Example 5.4 ($d_{\mathrm{W}}(p X, Z) \le p$) yields $|d_{\mathrm{W}}(p W, Z) - p\,d_{\mathrm{W}}(X, W)| \le d_{\mathrm{W}}(p X, Z) \le p$. Machine-checked refutation `not_Sec6_opening_wasserstein_printed` and reduction `opening_wasserstein_of_ex5_4` are proved in `Formalization/Geometric/OpeningBound.lean`.

---

### `ISSUE-6.4` — Boundary Degeneracy at $p = 1$ ($W \equiv 0$) for Discrete Equilibrium Uniqueness and Renewal Tail Formula
- **Source**: Preamble to Proposition 6.4 (`SteinIntro.tex:3290-3291`) and Remark 6.2 (`\label{rem175}`, `SteinIntro.tex:3304-3310`)
- **Printed text (verbatim)**:
  ```tex
  The following result provides a constructive definition of the discrete equilibrium distribution, so that the
  right hand side of \eq{1717} defines a probability distribution.
  \begin{proposition}\label{prop172}
  Let $W\geq0$ be an integer-valued random variable with $\IE[W]=(1-p)/p$ for some $0 \lt p\leq 1$ and let $W^s$ have the size-bias distribution
  of $W$.  If conditional on $W^s$, $W^e$ is uniform on $\{0, 1, \ldots, W^s-1\}$, then $W^e$
  has the discrete equilibrium distribution with respect to $W$.
  \end{proposition}
  ```
  ```tex
  \begin{remark}\label{rem175}
  This proposition shows that the equilibrium distribution is the same as that from renewal theory - see Remark~\ref{rem171}.
  \end{remark}
  ```
- **Counterexample (`not_unique_isDiscreteEquilibrium_one`)**: At $p = 1$, $\mathbb{E}[W] = (1 - 1)/1 = 0$ forces $W = 0$ a.s., and equation `(6.1)` (`p \mathbb{E}[f(W)] - p f(0) = (1 - p)\mathbb{E}[\Delta f(W^e)]`) reduces to $0 = 0 \cdot \mathbb{E}[\Delta f(W^e)]$, which is satisfied by **every** probability law on $\mathbb{N}$ (e.g., both $\delta_0$ and $\delta_1$, machine-checked in `Formalization/Geometric/Equilibrium.lean`), while the renewal stationary-excess formula $\mathbb{P}(W^e = k) = \frac{p}{1 - p}\mathbb{P}(W > k)$ divides by $1 - p = 0$.
- **Resolution**: `Prop6_4` holds for all $0 < p \le 1$ under the division-free joint conditional uniform hypothesis (`m = 0` is vacuous when $W = 0$ has no size-bias realization, or holds vacuously); `Rem6_2_restricted` restricts existence, uniqueness, and the stationary-excess tail formula to $0 < p < 1$.

---

### `ISSUE-7.5` — Stein Parameter $a = 2/(n - 1)$ Violates $a \le 1$ at $n = 2$ (and Divides by Zero at $n = 1$)
- **Source**: Example 7.5 and Proposition 7.3 (`SteinIntro.tex:3597-3625`)
- **Printed text**: For a uniform random permutation $\sigma$ of $\{1, \dots, n\}$ and uniform random transposition $\tau$, claims (`L3610`, `L3619`) that $(W, W')$ is a $\frac{2}{n - 1}$-Stein pair and applies Theorem 7.2 (`\label{thm211a}`).
- **Counterexample**: At $n = 2$ with $a_{11} = a_{22} = 1$ and $a_{12} = a_{21} = 0$, $W = \pm 1$ with equal probability and the unique transposition $\tau = (1\,2)$ gives $W' = -W$, so $\mathbb{E}[W' \mid W] = -W = (1 - 2)W$. Here $a = \frac{2}{2 - 1} = 2 > 1$, which violates Definition 3.2's requirement $0 < a \le 1$ (`L954`). Furthermore, at $n = 1$ no transposition exists and $2/(n - 1)$ divides by zero (though $W \equiv 0$ makes Proposition 7.3's inequality $\mathbb{P}(|W| \ge t) = 0 \le 2 e^{\dots}$ trivially true for $t > 0$).
- **Resolution (`D7`)**: Keep `0 < a ∧ a ≤ 1` in `IsSteinPair` as printed, prove the library concentration theorem (Theorem 7.2) for any `0 < a`, and use it directly to prove Proposition 7.3 for all $n \ge 2$ (with $n = 1$ handled trivially since $W \equiv 0$).

---

### `ISSUE-7.6` — Missing $t \ge 0$ Hypothesis in Size-Bias Concentration Theorem 7.6
- **Source**: Theorem 7.6 (`\label{thm211c}`, `SteinIntro.tex:3814-3826`)
- **Printed text**: States tail bounds $\mathbb{P}(\frac{X - \mu}{\sigma} \le -t) \le \exp(\frac{-t^2}{2 C \mu / \sigma^2})$ and $\mathbb{P}(\frac{X - \mu}{\sigma} \ge t) \le \exp(\frac{-t^2}{2(C \mu/\sigma^2 + C t/(2\sigma))})$ without stating $t \ge 0$ (unlike Proposition 7.1 `L3413` and Theorem 7.2 `L3485`, which print *"for all $t \ge 0$"*).
- **Counterexample**: Take $X \sim \mathrm{Bernoulli}(1/2)$ and $X^s \equiv 1 \ge X$ ($C = 1$, $\mu = 1/2$, $\sigma = 1/2$). At $t = -3 < 0$, $\mathbb{P}((X - \mu)/\sigma \le -(-3)) = \mathbb{P}(2X - 1 \le 3) = 1$, whereas $\exp(-(-3)^2 / (2 \cdot 2)) = e^{-9/4} < 1$.
- **Resolution**: Formalize `Thm7_6_corrected` quantifying `∀ t : ℝ, 0 ≤ t → ...` (note `0 < C` follows automatically from `0 < Var(X)` and `|X - X^s| ≤ C`).

---

## Part III — Unnumbered Prose & Reading Notes (Numbered Statements Are Literal)

### `ISSUE-3.3` (Reading Note on `L748-759` — Function Regularity in Lemma 3.3)
- **Source**: Preamble to Lemma 3.3 (`SteinIntro.tex:748-752`) and Lemma 3.3 (`\label{lem33}`, `SteinIntro.tex:753-759`)
- **Printed text (verbatim)**:
  - Surrounding context (`L750-752`): *"Since our strategy is to apply Theorem \ref{thm31} by estimating the right side of (3.2) for bounded $f$ with bounded first and second derivative, the first lemma shows an expansion of the right side of (3.2) using the structure of $W$ as defined in Theorem \ref{thm32}."*
  - Lemma 3.3 (`L754-758`): *"In the notation of Theorem \ref{thm32}, if $W_i = (\sum_{j \ne i} X_i)/\sqrt{n}$ then $\mathbb{E}[W f(W)] = \mathbb{E}\bigl[\frac{1}{\sqrt{n}}\sum_{i=1}^n X_i(f(W) - f(W_i) - (W - W_i)f'(W))\bigr] + \mathbb{E}\bigl[\frac{1}{\sqrt{n}}\sum_{i=1}^n X_i(W - W_i)f'(W)\bigr]$."*
- **Reading note**: Lemma 3.3 prints no explicit hypothesis on $f$, inheriting from `L750-751` the context of *"bounded $f$ with bounded first and second derivative"*. `SteinMethod.Lem3_3` assumes strictly less (`Differentiable ℝ f`, `f` bounded, and `deriv f` bounded, without requiring second-order differentiability or a bound on $f''$), under which all three expectations in `(3.3)`–`(3.4)` are Bochner-integrable, so `Lem3_3` implies the printed lemma under its surrounding context (`ISSUE-TYPO-3.3` covers the `X_j` summand typo in $W_i$).

---

### `ISSUE-3.14` (Reading Note on `L1289-1290` and `L1321-1322` — Unused Extra Independence Clauses in Proposition 3.14 and Corollary 3.15)
- **Source**: Recipe Item 1 for Proposition 3.14 (`\label{prop71}`, `SteinIntro.tex:1289-1291`) and Corollary 3.15 (`\label{cor71}`, `SteinIntro.tex:1319-1325`)
- **Printed text (verbatim)**:
  - Recipe Item 1 (`L1289-1291`): *"For each $i=1,\ldots, n$, let $X_i^{s}$ have the size-bias distribution of $X_i$ independent of $(X_j)_{j\not=i}$ and $(X_j^s)_{j\not=i}$. Given $X_i^s=x$, define the vector $(X_j^{(i)})_{j\not=i}$ to have the distribution of $(X_j)_{j\not=i}$ conditional on $X_i=x$."*
  - Corollary 3.15 (`L1320-1322`): *"Let $X_1, \ldots, X_n$ be non-negative independent random variables with $\mathbb{E}[X_i]=\mu_i$, and for each $i=1,\ldots, n$, let $X_i^{s}$ have the size-bias distribution of $X_i$ independent of $(X_j)_{j\not=i}$ and $(X_j^s)_{j\not=i}$."*
- **Reading note**:
  - In Proposition 3.14, the proof (`SteinIntro.tex:1300-1316`) uses only the joint conditional law of $(X_i^s, (X_j^{(i)})_{j \ne i})$ from Item 1 together with Item 2 (independence of $I$ from the summands and coupled variables) and Item 3; it never uses independence of $X_i^s$ from $(X_j)_{j \ne i}$ or $(X_j^s)_{j \ne i}$. `SteinMethod.Prop3_14` omits that unused clause and therefore assumes strictly less, implying the printed Proposition 3.14 under either reading (marginal vs. joint independence) of that clause.
  - Analogously, in Corollary 3.15, only `IndepFun (Xs i) (fun ω (j : {j // j ≠ i}) ↦ X j ω) P` is needed to identify $(X_j)_{j \ne i}$ as its own conditional version given $X_i^s$; `SteinMethod.Cor3_15` omits independence of $X_i^s$ from $(X_j^s)_{j \ne i}$ and therefore implies the printed Corollary 3.15 under either reading.

---

### `ISSUE-3.22` (Prose Note on `L1558-1561`) — Non-Centered Triangular Arrays in Prose Remark (`Thm3_22` and `Thm3_23` Are Literal)
- **Source**: Unnumbered triangular-array prose (`SteinIntro.tex:1558-1564`), Theorem 3.22 (`\label{thm82}`, `SteinIntro.tex:1568-1575`), and Theorem 3.23 (`\label{thm83}`, `SteinIntro.tex:1578-1581`)
- **Printed text (verbatim)**:
  - Unnumbered prose (`L1558-1564`): *"Let $(X_{i,n})_{1\leq n, 1\leq i \leq n}$ be a triangular array of random variables [footnote: That is, for each $n$, $(X_{i,n})_{1\leq i \leq n}$ is a collection of independent random variables.] such that $\mathrm{Var}(X_{i,n})=\sigma_{i,n}^2 \lt \infty$. Let $W_n=\sum_{i=1}^n X_{i,n}$, and assume that $\mathrm{Var}(W_n)=1$. A sufficient condition for $W_n$ to satisfy a CLT as $n\rightarrow\infty$ is the Lindeberg condition: for all $\varepsilon>0$, $\sum_{i=1}^n \mathbb{E}[X_{i, n}^2\mathbb{I}[|X_{i,n}|>\varepsilon]]\rightarrow 0$, as $n\rightarrow \infty$."*
  - Theorem 3.22 (`L1569-1574`): *"Let $(X_{i,n})_{1 \leq n, 1\leq i \leq n}$ be the triangular array defined above and let $I_n$ be a random variable independent of the $X_{i,n}$ and such that $\mathbb{P}(I_n=i)=\sigma_{i, n}^2$. For each $1\leq i \leq n$, let $X_{i,n}^z$ have the zero-bias distribution of $X_{i,n}$ independent of all else. Then the Lindeberg condition (3.34) holds if and only if $X_{I_n, n}^z \stackrel{p}{\rightarrow} 0$ as $n \to \infty$."*
  - Theorem 3.23 (`L1579-1580`): *"In the notation of Theorem \ref{thm82} and the remarks directly preceding it, if $X_{I_n, n}^z \to 0$ in probability as $n \to \infty$, then $W_n$ satisfies a CLT."*
- **Classification (`review-01.md` M4 — prose note, NOT a theorem defect)**:
  - Both Theorem 3.22 (`\label{thm82}`) and Theorem 3.23 (`\label{thm83}`) hypothesize that $X_{i,n}^z$ has the zero-bias distribution of $X_{i,n}$, and Definition 3.10 (`SteinIntro.tex:1442-1449`, formalized as `SteinMethod.IsZeroBias`) **already includes** $\mathbb{E}[X_{i,n}] = 0$. Therefore Theorems 3.22 and 3.23 hold literally as printed and are formalized as `Thm3_22` and `Thm3_23` (no `_corrected` suffix).
  - Only the unnumbered prose remark at `L1558-1561` (`"satisfy a CLT"`) is ambiguous if read as $W_n \stackrel{d}{\to} \mathcal{N}(0, 1)$ without centering: taking i.i.d. $\xi_{i,n} \sim \mathcal{N}(0, 1)$ and $X_{i,n} = n^{-3/4} + \xi_{i,n}/\sqrt{n}$ satisfies $\mathrm{Var}(W_n) = 1$ and the Lindeberg condition `(3.34)` (`\label{85}`), while $W_n \sim \mathcal{N}(n^{1/4}, 1)$ diverges unless centered as $W_n - \mathbb{E}[W_n]$.

---

### `ISSUE-3.25` (Proof Note on `L1679-1681` and `L1752-1768`) — Sharp Bound $\|f_x'\| \le 1$ Used in Theorem 3.28
- **Source**: Lemma 3.25 (`\label{lem91}`, `SteinIntro.tex:1679-1681`) and proof of Theorem 3.28 (`\label{thm92}`, `SteinIntro.tex:1752-1768`)
- **Note**: Lemma 3.25 states $\|f_x'\| \le 2$, whereas the proof of Theorem 3.28 (`L1763-1769`) bounds $|\mathbb{E}[f_x'(W)(1 - \frac{(W'-W)^2}{2a})]|$ with constant $1/(2a)$ rather than $2/(2a)$, tacitly using the sharp bound $\|f_x'\| \le 1$ ($0 < f_x'(w) < 1$ for $w < x$ and $-1 < f_x'(w) < 0$ for $w > x$, proved as `abs_derivWithin_Iic_normalSteinSolKolm_le_one` in `Formalization/Kolmogorov/SolutionBounds.lean`, matching Chen–Goldstein–Shao 2011 Lemma 2.3). Because $|D_- f_x(w)| \le 1$ holds for all $w \in \mathbb{R}$, Theorem 3.28's printed constant is true as printed (`Thm3_28` needs no constant adjustment; `Lem3_25_corrected` uses the left derivative per `ISSUE-2.2` and retains the printed bound `2`).

---

### `ISSUE-4.4` (Reading Note — `Lem4_4` Is Literal Under the Lemma 4.2 Reading)
- **Source**: Lemma 4.4 (`\label{lem103}`, `SteinIntro.tex:1879-1886`) and Lemma 4.2 (`\label{lem102}`, `SteinIntro.tex:1837-1848`)
- **Printed text (verbatim, `L1880-1885`)**: *"If $f_A$ solves (4.1), then $\|f_A\|\leq\min\left\{1, \lambda^{-1/2}\right\}$ and $\|\Delta f_A\|\leq \frac{1-e^{-\lambda}}{\lambda}\leq \min\left\{1, \lambda^{-1}\right\}$, where $\Delta f(k):=f(k+1)-f(k)$."*
- **Reading note (`review-01.md` M5)**:
  - At `L1880` (and the preceding sentence `L1878`, *"properties of the solutions $f_A$ of (4.1)"*), `"f_A"` denotes the canonical solution defined in Lemma 4.2 (`L1838-1843`), which satisfies the boundary condition $f_A(0) = 0$ (`poissonSteinSol r A 0 = 0`). Under this reading, Lemma 4.4 holds literally for all $k \ge 0$ and is formalized as `Lem4_4` (accepted in [`docs/COVERAGE.md`](COVERAGE.md)).
  - Under the alternative reading *"any solution $g$ of `(4.1)` without $g(0) = 0$"*, the claim fails at $k = 0$: equation `(4.1)` (`\lambda g(1) - 0 \cdot g(0) = \mathbb{I}[0 \in A] - \mathcal{P}_\lambda(A)`) places no constraint on $g(0)$, so for $\lambda = 1$ and $A = \emptyset$, $g(0) := 2$ and $g(k) := 0$ ($k \ge 1$) solves `(4.1)` for every $k \ge 0$ while $|g(0)| = 2 > 1 = \min\{1, 1^{-1/2}\}$ and $|\Delta g(0)| = 2 > 1 - e^{-1}$.

---

### `ISSUE-6.1` (Reading Note on `L3237` and `L3284` — Integer-Valued Support of $W$ in Section 6)
- **Source**: Lemma 6.1(2) (`\label{lem173}`, `SteinIntro.tex:3237-3238`) and Definition 6.1 (`SteinIntro.tex:3283-3289`)
- **Printed text (verbatim)**:
  - Lemma 6.1(2) (`L3237-3238`): `\item If for some non-negative random variable $W$, $\IE\%{A}f(W)=0$ for all bounded $f$, then $W\sim\Geo(p)$.`
  - Definition 6.1 (`L3284`): `Let $W\geq0$  a random variable with $\IE[W]=(1-p)/p$ for some $0 \lt p\leq 1$.`
- **Reading note**: Both $\mathcal{A}f(k) = (1 - p)\Delta f(k) - p f(k) + p f(0)$ (`L3232`) and Proposition 6.4 / Theorem 6.5 (`L3293, L3313`) evaluate forward differences $\Delta f$ on $\mathbb{N} = \{0, 1, 2, \dots\}$, so *"non-negative random variable $W$"* at `L3237` and `L3284` is read as $\mathbb{N}$-valued (`W : Ω → ℕ`) in `Lem6_1_2` and `IsDiscreteEquilibrium`.

---

### `ISSUE-6.6` (Proof Note on `L3348` and `L3384-3385` — Factor-of-$2$ Slack in Theorem 6.6)
- **Source**: Theorem 6.6 (`\label{thm1716}`, `SteinIntro.tex:3345-3350`) and its proof (`SteinIntro.tex:3384-3385`)
- **Printed text (verbatim)**:
  ```tex
  \begin{theorem}\label{thm1716} If $W$ is the in-degree of a node chosen uniformly
  at random from the random graph $G_n$ generated according to uniform attachment and $N\sim\Geo(1/2)$, then
  \bes
      \dtv(W, N)\leq \frac{2(\log(n)+1)}{n}.
  \ee
  \end{theorem}
  ```
- **Proof note**: Applying Theorem 6.5 (`d_{\mathrm{TV}}(W, N) \le 2(1 - p)\mathbb{E}|W^e - W|`) at $p = 1/2$ gives $2(1 - 1/2) = 1$, so $\mathbb{E}|W^e - W| = \frac{1}{n}\sum_{i=1}^n \frac{1}{n - i + 1} \le \frac{\log(n) + 1}{n}$ actually yields the sharper bound $d_{\mathrm{TV}}(W, N) \le \frac{\log(n) + 1}{n}$ (`tvDist_uniformAttachment_inDegree_le_sharp` in `Formalization/Geometric/UniformAttachment.lean`). Theorem 6.6's printed bound $\frac{2(\log(n) + 1)}{n}$ holds a fortiori for all $n \ge 1$ and is formalized verbatim as `SteinMethod.Thm6_6`.
