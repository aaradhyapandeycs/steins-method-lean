# Source Issues, Errata, Underspecifications, and Counterexamples (`arXiv:1109.1880v1`)

Per Rules 3–5 of [`AGENTS.md`](../AGENTS.md) and [`docs/AUTHOR_RULINGS.md`](AUTHOR_RULINGS.md) (`RULING-USER-2026-11-11`), this single ledger records every source typo, cross-reference bug, underspecification, and false-as-printed statement in Nathan Ross, *"Fundamentals of Stein's method"* (`SteinIntro.tex`, SHA-256 `02041ab1408158cebf82f2ec67fed7722ed7594b78728ca00d644a92d67d8d95`), together with verified counterexamples and the exact `_corrected` or `_restricted` Lean statement names declared in `Formalization/Statements/SecN.lean` (and proved in `Formalization/Statements/SecNProofs.lean`). Part III records unnumbered prose, proof, and reading notes whose numbered theorem statements are formalized literally without `_corrected` or `_restricted` suffixes.

---

## Part I — Source Typos and Cross-Reference Errata

### `ISSUE-TYPO-1.1` — Indicator Notation Typo and Stray Byte in Total Variation Definition
- **Source**: Section 1.1.1, item 3 (`SteinIntro.tex:520-521`)
- **Printed text**: `"By taking \mathcal{H}=\{\mathbb{I}[A\in\mathbb{R}]: A \in\mbox{Borel}(\mathbb{R})\} in (1.1), we obtain the total variation metric... We will use the total variation metric for approximation by Œdiscrete distributions."`
- **Issue**: `\mathbb{I}[A\in\mathbb{R}]` is a typo for the indicator function `\mathbb{I}[\cdot \in A]` (`A.indicator 1`), and `L521` contains a stray Latin-1 ligature byte (`0x8C`, `Œ`) before `discrete`.
- **Resolution**: `SteinMethod.tvDist` is defined via `{h : α → ℝ | ∃ A, MeasurableSet A ∧ h = A.indicator 1}` (`D1`, `D3`).

### `ISSUE-TYPO-2.1-PROOF` — Missing Leading Minus Sign on Second Integral in Proof of Lemma 2.1 (`SteinIntro.tex:632`)
- **Source**: Proof of Lemma 2.1 (`\label{lem1}`, `SteinIntro.tex:631-634`)
- **Printed text (verbatim, `L631-634`)**:
  ```tex
\IE f'(Z) &=\frac{1}{\sqrt{2\pi}} \int_\IR e^{-t^2/2} f'(t) dt \\
	&=\frac{1}{\sqrt{2\pi}} \int_0^\infty f'(t)\int_t^\infty w e^{-w^2/2} dw dt +\frac{1}{\sqrt{2\pi}}  \int_{-\infty}^0 f'(t)\int_{-\infty}^t w e^{-w^2/2} dw dt \\
	&=\frac{1}{\sqrt{2\pi}} \int_0^\infty w e^{-w^2/2} \left[ \int_0^w f'(t) dt \right]dw +\frac{1}{\sqrt{2\pi}}  \int_{-\infty}^0 w e^{-w^2/2} \left[ \int_w^0 f'(t) dt \right]dw \\
	&=\IE[Zf(Z)].
  ```
- **Issue**: For $t \lt 0$, $\int_{-\infty}^t w e^{-w^2/2}\,dw = -e^{-t^2/2}$, so the second integral on `L632` requires a leading minus sign (which propagates through `L633` to give `L634`; at $f(w) = w$, `L631` and `L634` equal $1$, whereas the printed `L632` and `L633` evaluate to $0$). Lemma 2.1 (`Lem2_1_1`, `Lem2_1_2`) is unaffected.

### `ISSUE-TYPO-2.0-PRIME` — Missing Derivative Prime `'` on `f_x(W)` in Section 2 Transition Prose (`SteinIntro.tex:648`)
- **Source**: Section 2 transition prose (`SteinIntro.tex:646-651`)
- **Printed text (verbatim, `L646-651`)**:
  ```tex
Our strategy for bounding the maximum distance between the distribution function of a random variable $W$ and that
of the standard normal is now fairly obvious: we want to bound
$\IE[f_x(W)-Wf_x(W)]$ for $f_x$ solving \eqref{1a}.  This setup can work, but it turns out that it is easier to work in
the Wasserstein metric.  Since the critical property of the Kolmogorov metric that we use in the discussion above is
the representation \eq{23}, which the Wasserstein metric shares, extending in this direction comes without great effort.
  ```
- **Issue**: Line 648 prints `\IE[f_x(W)-Wf_x(W)]` in place of `\IE[f'_x(W)-Wf_x(W)]`.

### `ISSUE-TYPO-SEC3-OPEN` — `"Proposition \ref{lem31}"` for Lemma 2.5 in Section 3 Opening (`SteinIntro.tex:713, 715`)
- **Source**: Section 3 opening paragraph (`SteinIntro.tex:711-716`)
- **Printed text (verbatim, `L711-716`)**:
  ```tex
The reason for using the Wasserstein metric is that it has the form \eqref{32} for $\%H$ the set of functions with Lipschitz constant equal to one.
In particular, if $h$ is a test function for the Wasserstein metric, then $\norm{h'}\leq1$ so that we know the solution $f_h$ of equation
\eqref{33} is bounded with two bounded derivatives by Item \ref{i32} of Proposition \ref{lem31}.  Contrast this to the set of test functions for the Kolmogorov metric where the solution $f_h$ of equation
\eqref{33} is bounded with
one bounded derivative (by Item \ref{i31} of Proposition \ref{lem31}) but is not twice differentiable.   
  ```
- **Issue**: Lines 713 and 715 refer to `\ref{lem31}` as `"Proposition 2.5"` rather than `"Lemma 2.5"`. Under the project's accepted a.e./Lipschitz reading of Lemma 2.5(2) (`Lem2_5_2`), `Sec3_opening_steinSol_regularity` proves the $2$-Lipschitz first-derivative regularity of $f_h$ for $1$-Lipschitz $h$ (while `not_sec3_normalSteinSol_mem_wassersteinClass_strictReading_proof` in `Formalization/Sweep/SweepASec3a.lean` records that $f_h'$ need not be everywhere differentiable at corners of $h$).

### `ISSUE-TYPO-3.5-PROOF` — Missing `1/\sigma` Normalization in Definition of `W_i` in Proof of Theorem 3.5 (`SteinIntro.tex:832`)
- **Source**: Proof of Theorem 3.5 (`\label{thm41}`, `SteinIntro.tex:832-833`)
- **Printed text (verbatim, `L832-833`)**:
  ```tex
$\norm{f}, \norm{f''}\leq 2$ and $\norm{f'}\leq \sqrt{2/\pi}$.  Define $W_i=\sum_{j\not\in N_i} X_j$ and note that $X_i$ is independent
of $W_i$.  As in the proof of Theorem \ref{thm32}, %%%XXXXX
  ```
- **Issue**: `L832` omits the $1/\sigma$ normalization in $W_i = \frac{1}{\sigma}\sum_{j \notin N_i} X_j$, which is used throughout `L836-860` ($W - W_i = \frac{1}{\sigma}\sum_{j \in N_i} X_j$).

### `ISSUE-TYPO-3.3` — Summand Index Typo in Lemma 3.3
- **Source**: Lemma 3.3 (`\label{lem33}`, `SteinIntro.tex:754`)
- **Printed text**: `"In the notation of Theorem \ref{thm32}, if W_i = (\sum_{j\not=i} X_i)/\sqrt{n} then..."`
- **Issue**: Summing $X_i$ over $j \ne i$ yields $(n-1)X_i/\sqrt{n}$, which is neither independent of $X_i$ (`L766`) nor satisfies $W - W_i = X_i/\sqrt{n}$ (`L788`). The intended summand is $X_j$: $W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$.
- **Resolution**: Formalize Lemma 3.3 with $W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$ (equivalently $W - X_i/\sqrt{n}$).

### `ISSUE-TYPO-3.2.1` — Metric Symbol Typo in Section 3.2.1 (Literal $d_{\mathrm{K}}$ Bound Also Proved for $0 \lt p \lt 1$)
- **Source**: Section 3.2.1 (`SteinIntro.tex:936`)
- **Printed text**: `"\dk(W, Z) \le ..."` when applying Theorem 3.5 (`\label{thm41}`) to triangle counts in $G(n, p)$.
- **Issue**: Theorem 3.5 bounds the Wasserstein distance $d_{\mathrm{W}}(W, Z)$, not $d_{\mathrm{K}}(W, Z)$.
- **Resolution**: `Sec3_2_1_triangles_restricted` formalizes the Theorem 3.5 Wasserstein bound (`wassersteinDist`), while `Sec3_2_1_triangles_kolmogorov_restricted` (`SteinMethod.erdosRenyi_triangles_kolmogorovDist_le` in `Formalization/Leftovers/TrianglesKolm.lean`) independently proves via monotone coordinate-replacement Stein's method, Boolean Efron–Stein, and rational sum-of-squares dominance that the literal printed Kolmogorov-distance bound (`kolmogorovDist`) **also holds unconditionally** for all $n \ge 3$ and $0 \lt p \lt 1$.

### `ISSUE-TYPO-3.5` — Cross-Reference `Theorem \ref{51}` Instead of `Theorem \ref{thm51}` in Remark 3.5 and Example 3.6
- **Source**: Remark 3.5 (`SteinIntro.tex:1020`) and Example 3.6 (`SteinIntro.tex:1096`)
- **Printed text (verbatim)**:
  - `L1020`: `"What does this have to do with Theorem \ref{51}?"`
  - `L1096`: `"Finally, we could probably get away with only assuming three moments for the $X_i$ if we use the intermediate term \eqref{511} in the proof of Theorem \ref{51}."`
- **Issue**: `\label{51}` is the equation label of display `(3.16)` (`SteinIntro.tex:1032`, inside the proof of Theorem 3.7), so LaTeX prints `"Theorem 3.16"` at both `L1020` and `L1096` instead of `"Theorem 3.7"` (`\ref{thm51}`, which is used on `L1010`, `L1022`, and `L1070`).

### `ISSUE-TYPO-3.4a` — Missing Expectation Operator in Display `(3.23)`
- **Source**: Section 3.4, display `(3.23)` (`\label{71}`, `SteinIntro.tex:1232-1236`)
- **Printed text**: `\mathbb{E}[W f(W)] = \frac{\mu}{\sigma}\left[f\left(\frac{X^s-\mu}{\sigma}\right) - f\left(\frac{X-\mu}{\sigma}\right)\right]`.
- **Issue**: The right-hand side is a random variable whereas the left-hand side is deterministic; `\mathbb{E}` is omitted before the bracket on the right-hand side.
- **Resolution**: Formalize `Sec3_4_sizeBias_identity` with expectation on the right-hand side (together with `Integrable (fun ω ↦ f ((Xs ω - μ) / σ)) P`).

### `ISSUE-TYPO-3.14` — Proof of Proposition 3.14 Writes Undefined `W` for the Sum `X` (`SteinIntro.tex:1304, 1306`)
- **Source**: Proof of Proposition 3.14 (`\label{prop71}`, `SteinIntro.tex:1296-1308`)
- **Printed text (verbatim, `L1303-1307`)**:
  ```tex
  \ban
  \IE[Wf(\textbf{X})]=\mu\IE[f(\textbf{X}^I)], \label{77aa}
  \ee
  for $f:\IR^n\rightarrow \IR$ such that $\IE|Wf(\textbf{X})|< \infty$.  Equation \eq{77aa} follows easily after we show that for all $i=1, \ldots, n$,
  \ban
  ```
- **Issue**: On `L1304` (`\IE[Wf(\textbf{X})]=\mu\IE[f(\textbf{X}^I)], \label{77aa}`) and `L1306` (`\IE|Wf(\textbf{X})|< \infty`), `W` is undefined in §3.4: Proposition 3.14 (`L1297`) defines `X=\sum_{i=1}^n X_i`, and summing `\IE[X_i f(\textbf{X})]=\mu_i\IE[f(\textbf{X}^i)]` (`L1308`) over $i = 1, \dots, n$ shows both occurrences of `W` should be the sum `X` (`SteinMethod.Prop3_14` is unaffected). (Separately, `L1159` inside the proof of Theorem 3.8 has the minor spelling typo `"different labal"` for `"different label"`.)

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

### `ISSUE-TYPO-THM4.8` — Outer Sum Upper Limit `n` Instead of `n - k + 1` in Proof of Theorem 4.8
- **Source**: Proof of Theorem 4.8 (`\label{thm104}`, `SteinIntro.tex:2046-2048`)
- **Printed text (verbatim, `L2046-2048`)**:
  ```tex
  \ba
  \dtv(W, Z)\leq \sum_{i=1}^n\sum_{j\in N_i} \IE[X_i]\IE[X_j].
  \ee
  ```
- **Issue**: Because the de-clumped head-run indicators $X_i$ and dependency neighborhoods $N_i$ are indexed for $1 \le i \le n - k + 1$ (`L2015-2023`), the outer sum's upper limit `n` is a cosmetic typo for $n - k + 1$ (under $X_i \equiv 0$ for $i \gt n - k + 1$, the printed sum evaluates identically; dropping Theorem 4.7's factor $\min\{1, \lambda^{-1}\}\le 1$ is a valid weakening). Theorem 4.8 (`Thm4_8`) is unaffected.

### `ISSUE-TYPO-4.11` — Unbound Variable `X` in Conclusion of Corollary 4.11
- **Source**: Corollary 4.11 (`\label{cor121}`, `SteinIntro.tex:2142-2147`)
- **Printed text (verbatim, `L2145-2146`)**:
  ```tex
  $I$ is a random variable independent of all else such that $\IP(I=i)=p_i/\lambda$, then $W^s=\sum_{j\not=I} X_j^{(I)} +1$
  has the size-bias distribution of $X$.
  ```
- **Issue**: Line 2143 defines $W = \sum_{i=1}^n X_i$ (not $X$, which was the notation of Corollary 3.16 at `L1326-1332`); `"of $X$"` at `L2146` is a copy-paste typo for `"of $W$"`. Formalized with $W = \sum_{i=1}^n X_i$ in `SteinMethod.Cor4_11`.

### `ISSUE-TYPO-4.12` — Unbound `X`, `X^s` and Doubled `"and"` in Corollary 4.12
- **Source**: Corollary 4.12 and its proof (`\label{cor122}`, `SteinIntro.tex:2148-2159`)
- **Printed text (verbatim, `L2152-2157`)**:
  ```tex
  If $W=\sum_{i=1}^n X_i$, then the size-bias distribution of $X$ can be represented
  by $X^s=\sum_{j\not=1}X_j^{(1)} + 1$.
  \end{corollary}
  \begin{proof}
  Corollary \ref{cor121} was proved in Section \ref{sbc} and 
  and Corollary \ref{cor122} follows from the fact that exchangeability
  ```
- **Issue**: Lines 2152–2153 print `X` and `X^s` instead of `W` and `W^s` (`W = \sum_{i=1}^n X_i`), and lines 2156–2157 repeat `"and"`. Formalized for $W = \sum_{i=1}^n X_i$ in `SteinMethod.Cor4_12` (requiring $n \ge 1$ so index $1$ exists).

### `ISSUE-TYPO-EX4.6` — Copy-Paste `"isolated vertices"` in Example 4.6 (*Degree $d$ vertices*)
- **Source**: Example 4.6 (`SteinIntro.tex:2220-2246`)
- **Printed text (verbatim, `L2239-2240`)**:
  ```tex
  so that by Corollary \ref{cor122}, we can take $W^s=\sum_{j\not=1}X_j^{(1)} + 1$ and of course we take $W$
  to be the number of isolated vertices in $G$. 
  ```
- **Issue**: Copy-pasted from Example 4.5 (`L2194-2195`); as defined at `L2221-2224`, in Example 4.6 $W = \sum_{i=1}^n X_i$ is the number of degree-$d$ vertices in $G$. Formalized for degree-$d$ vertices in `SteinMethod.Ex4_6` (under $0 \lt n$ and $d \lt n$, since `L2231-2233` chooses $d - d_1$ non-neighbors from $n - d_1 - 1$ vertices).

### `ISSUE-TYPO-4.8` — Extraneous Factor $p^k$ in Display for $|\Gamma|$ in Example 4.8
- **Source**: Example 4.8 (*$k$-cycles*, `SteinIntro.tex:2358-2362`)
- **Printed text (verbatim, `L2358-2362`)**:
  ```tex
  To interpret this bound asymptotically, we note that
  $\lambda=\abs{\Gamma}p^k$ and 
  \ba
  \abs{\Gamma}=\binom{n}{k}\frac{(k-1)!}{2}p^k,
  \ee
  ```
- **Issue**: $\Gamma$ (`L2286`) is the deterministic set of all copies of a $k$-cycle in $K_n$, whose cardinality is $|\Gamma| = \binom{n}{k}\frac{(k-1)!}{2}$, whereas $\lambda = |\Gamma| p^k = \binom{n}{k}\frac{(k-1)!}{2} p^k$. Display `L2361` mistakenly repeats the factor $p^k$ on the right-hand side of $|\Gamma|$ (refuted at $k = 3, n = 3, p = 1/2$, where $|\Gamma| = 1 \ne 1/8$, as `SteinMethod.not_Ex4_8_L2361_printed` in `Formalization/PoissonSizeBias/Subgraph/Cycles.lean`). Formalized with $|\Gamma| = \binom{n}{k}\frac{(k-1)!}{2}$ in `SteinMethod.Ex4_8`.

### `ISSUE-TYPO-4.8-PROSE` — `"equality"` for `"inequality"` and `"non-isomorphic"` for `"distinct"` in Example 4.8
- **Source**: Example 4.8 (*$k$-cycles*, `SteinIntro.tex:2348-2352, 2363-2364`)
- **Printed text (verbatim)**:
  - `L2348-2352`: `\abs{\Gamma_\alpha^t}\leq \binom{k}{k-t}c_t n^{t-1}\leq C_k n^{t-1},` ... `"The second equality follows by maximizing $\binom{k}{k-t}c_t$ over the possible values of $t$."`
  - `L2363-2364`: `"since the number of non-isomorphic $k$-cycles on $K_k$ is $k!/(2k)$ (since $k!$ is the number of permutations of the vertices, which over counts by a factor of $2k$ due to reflections and rotations)."`
- **Issue**: At `L2352`, `"second equality"` means `"second inequality"` (referring to $\le C_k n^{t - 1}$ in `L2348`); at `L2363`, `"non-isomorphic $k$-cycles"` means `"distinct (unlabeled) $k$-cycles"` (all $k$-cycles are isomorphic as graphs).

### `ISSUE-TYPO-4.17` — Subscript Typo `\textbf{Y}=(Y_i)_{j=1}^N` in Theorem 4.17
- **Source**: Theorem 4.17 (`\label{thm124}`, `SteinIntro.tex:2383`)
- **Printed text (verbatim, `L2383`)**: `Let $\textbf{Y}=(Y_i)_{j=1}^N$ be a finite collection of independent indicators`
- **Issue**: Mismatched index `Y_i` vs `j=1..N`; intended `(Y_j)_{j=1}^N`.

### `ISSUE-TYPO-4.13` — Misprinted Factor `(n - m)` for `(N - m)` in Hypergeometric Variance (`SteinIntro_utf8.tex:2500`)
- **Location**: Example 4.13 (`[Hypergeometric distribution]`), `SteinIntro_utf8.tex` line 2500:
  `\IE[W]=\frac{nm}{N} \mbox{\, and \,} \var(W) = \frac{nm (N-n) (n-m)}{N^2 (N-1)},`
- **Issue**: The third numerator factor `(n - m)` is a typo for `(N - m)`. At $N = 4, n = 1, m = 2$,
  $W \sim \mathrm{Bernoulli}(1/2)$ has $\mathrm{Var}(W) = 1/4$, whereas the printed formula
  gives $-1/8 \lt 0$. Note that line 2504 already uses the corrected variance
  $\frac{nm(N - n)(N - m)}{N^2(N - 1)}$ when simplifying $1 - \mathrm{Var}(W)/\lambda$.
- **Formalization**: Refuted as printed by `not_Ex4_13_var_printed` (`not_ex4_13_var_printed`) and
  corrected in `Ex4_13_moments_corrected` (`ex4_13_moments_corrected`).

### `ISSUE-TYPO-REM4.17` — Missing Subject `"we"` in Remark 4.17 (`SteinIntro_utf8.tex:2600`)
- **Location**: Remark 4.17, `SteinIntro_utf8.tex` line 2600:
  `Finally, could also consider the number of boxes containing exactly $m\geq0$ balls and containing at least $m\geq1$ balls, Theorem \ref{thm122} applies to the latter problem.  See Chapter 6 of \cite{bhj92}.`
- **Issue**: Grammatical omission of `"we"` (`"Finally, we could also consider..."`); see also
  `ISSUE-REM-4.17` for the substantive cross-reference error (`\ref{thm122}` vs `\ref{thm125}`) in
  the same sentence.

### `ISSUE-TYPO-4.20` — Missing `\min` in Proof of Theorem 4.20
- **Source**: Proof of Theorem 4.20 (`SteinIntro.tex:2645`)
- **Printed text (verbatim, `L2645`)**:
  ```tex
  $\norm{f}\leq \min\{1, \lambda^{-1/2}\}$ and $\norm{\Delta f}\leq \{1, \lambda^{-1}\}$.  Now, the
  ```
- **Issue**: Missing `\min` before `\{1, \lambda^{-1}\}` in the proof prose (cf. Lemma 4.4, `SteinIntro.tex:1879-1886`).
- **Resolution**: Proof prose typo only; Theorem 4.20 (`SteinIntro.tex:2618-2626`) is unaffected, and `tvDist_poissonLaw_exchangeable_le` proves the exact printed Theorem 4.20 bound with $\min\{1, \lambda^{-1/2}\}$.

### `ISSUE-TYPO-EX4.21` — `"final inequality"` for `"final equality"` in Example 4.21 (`SteinIntro.tex:2701`)
- **Source**: Example 4.21 (`SteinIntro.tex:2695-2701`)
- **Printed text (verbatim, `L2695-2701`)**:
```tex
\ba
\dtv(W, Z)&\leq \IE\left|1-\frac{n-W-2W_2}{n}\right|
+\IE\left|W-\frac{W(n-W)}{n}\right| \\
&=\frac{1}{n}\IE\left[W+2W_2\right]+\frac{1}{n}\IE[W^2]\\
&=4/n,
\ee
where the final inequality follows by considering $W$ and $W_2$ as a sum of indicators which leads
```
- **Issue**: Line 2701 writes `"where the final inequality follows by considering $W$ and $W_2$ as a sum of indicators"`, referring to `&=4/n,` on `L2699`, which is an **equality** (`=`), not an inequality. Example 4.21 (`Ex4_21`) is unaffected.

### `ISSUE-TYPO-5.4` — `"no greater than"` Slip for `"no less than"` in Example 5.4
- **Source**: Example 5.4 (`\label{ex171}`, `SteinIntro.tex:2885-2886`)
- **Printed text (verbatim, `L2885-2886`)**:
  ```tex
  It is well known that as $p\to0$, $pN$ converges weakly to an exponential distribution; this fact is not surprising as a simple
  calculation shows that if $Z\sim\Exp(\lambda)$, then the smallest integer no greater than $Z$ is geometrically distributed.  We can use
  ```
- **Issue**: Because the set of integers $\le Z$ has no minimum, *"the smallest integer no greater than $Z$"* does not exist. Matching the positive-support geometric distribution $\mathrm{Ge}(p)$ on $\{1, 2, \dots\}$ defined on the preceding line (`L2884`), the intended random variable is $\lceil Z \rceil$ (*"the smallest integer no less than $Z$"*), which satisfies $\lceil Z \rceil \sim \mathrm{Ge}(1 - e^{-\lambda})$ for $Z \sim \mathrm{Exp}(\lambda)$ ($\lambda \gt 0$).
- **Resolution**: Formalize `Ex5_4_ceil_corrected` (`ex5_4_ceil_corrected` in `Formalization/Exponential/Basic.lean`).

### `ISSUE-TYPO-5.3a` — Misplaced Closing Parenthesis `\IP(Z_1=1<1)` in Section 5.3 Extinction Dichotomy
- **Source**: Section 5.3 opening (`SteinIntro.tex:3003-3004`)
- **Printed text (verbatim, `L3003-3004`)**:
  ```tex
It is a basic fact \cite{atne72} that if $\IE[Z_1]\leq 1$ and $\IP(Z_1=1<1)$ then the population almost surely dies out, whereas 
if $\IE[Z_1]>1$, then the probability the population lives forever is strictly positive.
  ```
- **Issue**: `\IP(Z_1=1<1)` is a LaTeX parenthesis typo for `\IP(Z_1=1)<1` (excluding the deterministic critical case $Z_1 = 1$ a.s. where $Z_n = 1$ for all $n$). Formalized as `P.real {ω | Z 1 ω = 1} < 1` in `Sec5_3_extinction`.

### `ISSUE-TYPO-5.3b` — Missing Superscript `s` in `G_n(t_i, v)` in Recursion for Equation (5.7)
- **Source**: Proof of Equation `(5.7)` (`\label{1710}`, `SteinIntro.tex:3091-3093`)
- **Printed text (verbatim, `L3091-3093`)**:
  ```tex
\ba
G_{n+1}^s(t,v)=G_n(t_i, v)\prod_{j\not=i} G_n(t_j)[k\IP(Z_1=k)]\frac{1}{k}.
\ee 
  ```
- **Issue**: The two-argument tree probability with a distinguished generation-$n$ vertex is $G_n^s(t_i, v)$ (`L3050-3052`), not $G_n(t_i, v)$, as confirmed by `L3094-3095`. Formalized with `gwSizeBiasProbV` in `Formalization/Defs/Branching.lean` (`Sec5_3_eq_1710`).

### `ISSUE-TYPO-5.3c` — `1 - U` Instead of `U` in Coupling Difference `|Y_n - Y_n^e|`
- **Source**: Proof of Theorem 5.9 (`SteinIntro.tex:3142-3145`)
- **Printed text (verbatim, `L3142-3145`)**:
  ```tex
\ba
\abs{Y_n-Y_n^e}&=\left|1-U+\sum_{j=1}^n(R_{n,j}' - R_{n,j}) \I[L_{n,j}>0]\right| \\
	&\leq \abs{1-U}+\sum_{j=1}^nR_{n,j}'\I[L_{n,j}>0]+\sum_{j=1}^nR_{n,j}\I[L_{n,j}>0].
\ee
  ```
- **Issue**: Since $Y_n = R_n^* = 1 + \sum_{j=1}^n \bigl(R_{n,j} + (R_{n,j}' - R_{n,j})\mathbf{1}_{L_{n,j} \gt 0}\bigr)$ (`L3134-3138`) and $Y_n^e = R_n - U = 1 + \sum_{j=1}^n R_{n,j} - U$ (`L3066`, `L3124`), the leading constants $1$ cancel and $-(-U) = +U$, giving $Y_n - Y_n^e = U + \sum_{j=1}^n (R_{n,j}' - R_{n,j})\mathbf{1}_{L_{n,j} \gt 0}$ rather than $1 - U + \dots$ (harmless in expectation since $U$ and $1 - U$ both have expectation $1/2$). Formalized with $U$ in `Sec5_3_eq_3143_corrected`.

### `ISSUE-TYPO-5.3d` — Minor Editorial Typos in Section 5.3 (`L2998`, `L3182`)
- **Source**: Section 5.3 (`SteinIntro.tex:2998` and `SteinIntro.tex:3182`)
- **Printed text (verbatim)**:
  - `L2998`: `We think of of $Z_n$ as the generation size of a population that initially has one individual and where` (duplicated word `"of of"`).
  - `L3182`: `&\leq \IE\left[X_j\IP(Z_{n-j}>0\right] \\` (missing closing parenthesis `)` in `\IP(Z_{n-j}>0`).

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


### `ISSUE-TYPO-7.4` — Missing `k \neq i` in Interaction Sum (`L3713, L3717`), `\s'_i` on LHS (`L3712, L3716`), and Missing Subscript `i` in `m'` (`L3777`) in Proof of Proposition 7.4
- **Source**: Proof of Proposition 7.4 (`\label{prop2112y}`, `SteinIntro.tex:3711-3721, 3765, 3777`)
- **Printed text (verbatim, `L3711-3721` and `L3777`)**:
```tex
\begin{split}
\IP(\s'_i = 1 , (\s_j)_{j \neq i} ) & =  Z^{-1} \exp \left\{
  \frac{\beta}{n} \left( \sum_{k < j, j \neq i} \sigma_j \sigma_k
    + \sum_{j \neq i} \s_j \right) + \beta h \sum_{j \neq i} \sigma_j
  + \beta h \right\}    ,\\
\IP(\s'_i = -1 , (\s_j)_{j \neq i} ) & =  Z^{-1} \exp \left\{
  \frac{\beta}{n} \left( \sum_{k < j, j \neq i} \sigma_j \sigma_k
    - \sum_{j \neq i} \s_j \right) + \beta h \sum_{j \neq i} \sigma_j
  - \beta h \right\}   . \\
\end{split}
\]
```
```tex
Also, if we denote $m' := \frac{1}{n} \sum_{i=1}^n \s'$, then
```
- **Issues & Numerical Verification**:
  1. *Omitted `k \neq i` in `\sum_{k < j, j \neq i} \sigma_j \sigma_k` (`L3713, L3717`) and `\s'_i` on LHS (`L3712, L3716`)*: Splitting $\sum_{k \lt j} \sigma_k \sigma_j$ in `(7.6)` (`L3634`) around site $i$ leaves pairs $\{k \lt j : j \ne i, k \ne i\}$. Without $k \ne i$, at $n = 3, i = 1, \sigma = (+1, +1, +1), h = 0, \beta = 1$, every pair $(k, j)$ with $1 \le k \lt j \le 3$ satisfies $j \ge 2 \ne 1$, so the printed exponent evaluates to $\frac{1}{3}(3 + 2) = \frac{5}{3} \ne 1 = \frac{1}{3}(1 + 2)$ (and for general $\sigma$, $k = i$ leaves $\sigma_i$ unbound inside the sum). Also `L3712, L3716` write `\s'_i` on the LHS instead of `\s_i` (cf. `L3701, L3703, L3708`). Because the $(k, j)$-sum cancels in the ratio `L3725-3735`, `(7.7)` and Proposition 7.4 (`Prop7_4`) are unaffected.
  2. *Missing subscript `i` on `\s'` (`L3777`) and `B, C > 0` before `B = 0` (`L3765, L3786`)*: `m' := \frac{1}{n} \sum_{i=1}^n \s'` omits subscript `i` (intended `\s'_i`, cf. `L3643, L3693`), and `L3765` asks for `B, C > 0` before choosing `B = 0` at `L3786` (Theorem 7.5 at `L3667` allows `B, C \geq 0`).
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
- **Resolution**: Formalize both `Sec3_2_1_triangles_restricted` (`wassersteinDist`, from Theorem 3.5 per `ISSUE-TYPO-3.2.1`) and `Sec3_2_1_triangles_kolmogorov_restricted` (`kolmogorovDist`, proving the literal printed inequality at `L936-939` unconditionally on the interior domain) under `3 ≤ n`, `0 < p`, and `p < 1` (for which $\sigma \gt 0$). At $p \in \{0, 1\}$, $\sigma = 0$ makes $W = (T - \mathbb{E}[T])/\sigma$ and both RHS denominators ill-posed (class D). Likewise, in `Sec3_2_1_triangles_setup_and_moments` (`SteinIntro.tex:919-928`), `IsDependencyGraph` and the $k$-th central moment formula hold for all $0 \le p \le 1$, whereas the `L921-922` pairwise-independence `"if and only if"` criterion requires $0 \lt p \lt 1$ (at $p \in \{0, 1\}$ and $n \ge 4$, $Y_i$ is constant hence independent of $Y_j$ even when $|V_i \cap V_j| = 2$).
- **Addendum on the asymptotic CLT prose claim (`SteinIntro.tex:942-944`)**:
  - Printed text (`L942-944`): *"but some asymptotic analysis shows that if, for example, $p\sim n^{-\alpha}$ for some $0\leq \alpha \lt 1$ (so that $\mathrm{Var}(T)\rightarrow\infty$), then the number of triangles satisfies a CLT for $0\leq \alpha \lt 2/9$,"*
  - At $\alpha = 0$, the literal asymptotic relation $p_n \sim n^{-0} = 1$ ($\lim_{n \to \infty} n^0 p_n = 1$) allows both $p_n \equiv 1$ (where $\mathrm{Var}(T_n) = 0$ for all $n$, machine-checked as `SteinMethod.triangles_clt_counterexample_p_eq_one`) and strictly interior sequences such as $p_n = 1 - n^{-5} \in (0, 1)$ (where $\sigma_n \gt 0$ for $n \ge 3$ yet $\mathrm{Var}(T_n) = O(n^{-1}) \to 0 \not\to \infty$ and $\mathbb{P}(T_n = \binom{n}{3}) \to 1$).
  - Under $\lim_{n \to \infty} n^\alpha p_n = c \gt 0$, `Sec3_2_1_triangles_clt_regime_restricted` excludes only $c \ge 1$ at $\alpha = 0$ (`α = 0 → c < 1`), proving $\mathrm{Var}(T_n) \to \infty$ for all $0 \le \alpha \lt 1$ and $d_{\mathrm{W}}(W_n, Z) \to 0$, $d_{\mathrm{K}}(W_n, Z) \to 0$ for all $0 \le \alpha \lt 2/9$. At the threshold $\alpha = 2/9$ with $p_n = n^{-2/9}$, the printed Stein upper bound converges to $3\sqrt{2} \gt 0$ (`SteinMethod.triangles_bound_tendsto_at_two_ninths`), confirming that $2/9$ is the sharp threshold of `L937-938`.


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
  - *First failing proof step (`L855`)*: The step $\sum_{i=1}^n \sum_{j, k \in N_i} \mathbb{E}|X_j|^3 \le D^2 \sum_{j=1}^n \mathbb{E}|X_j|^3$ requires each index $j$ to belong to at most $D$ neighborhoods $N_i$ (which holds when $j \in N_i \iff i \in N_j$, i.e. symmetric neighborhoods, but fails under Definition 3.1 alone: for $N_1 = \{1\}$ and $N_i = \{1, i\}$ for $2 \le i \le n$, $D = 2$ while $\mathbb{E}|X_1|^3$ has coefficient $2n - 1 \gt 4 = D^2$ for $n \ge 3$).
  - *Second failing proof step (`(3.15)`)*: In `(3.15)` (`\label{43}`, `SteinIntro.tex:882-894`), Ross splits $\sum_{i \ne j}\sum_{k \in N_i}\sum_{l \in N_j}\mathbb{E}[X_i X_j X_k X_l]$ into a first sum over index tuples where $\{X_i, X_k\}$ is independent of $\{X_j, X_l\}$ and a second sum over the remaining tuples, then bounds the second sum by $6 D^3 \sum_{i=1}^n \mathbb{E}[X_i^4]$ via index-tuple counting (`L890-891`: *"since the number of 'connected components' with at most four vertices of the dependency graph induced by the neighborhoods, is no more than $D \times 2D \times 3D$"*). Definition 3.1 alone neither requires $i \in N_i$ nor implies that $\{X_i, X_k\}$ is independent of $\{X_j, X_l\}$ outside the counted neighborhood tuples: in the $n = 2m$ construction above, $X_{2r-1} X_{2r} = S = X_{2s-1} X_{2s}$ for all $m(m-1)$ pairs $r \ne s$, so $\Theta(m^2)$ four-tuples fail independence rather than $O(D^3 m)$.
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

### `ISSUE-4.4-PROSE` — False Sign Claim $\Delta f_0(k) \lt 0$ at $k = 0$ in Proof of Lemma 4.4
- **Source**: Proof of Lemma 4.4 (`\label{lem103}`, `SteinIntro.tex:1898-1900`)
- **Printed text (verbatim, `L1898-1900`)**:
  ```tex
  \end{itemize}
  And also $\Delta f_0(k)<0$.  Since
  \ba
  ```
- **Counterexample (`not_Sec4_fwdDiff_f0_neg_printed`)**: For any $\lambda \gt 0$ and $f_0 := f_{\{0\}}$, $f_0(0) = 0$ (`L1843`) and $\lambda f_0(1) - 0 \cdot f_0(0) = \mathbb{I}[0 \in \{0\}] - \mathrm{Po}(\lambda)(\{0\}) = 1 - e^{-\lambda}$ (`L1841`), so at $k = 0$,
  $$\Delta f_0(0) = f_0(1) - f_0(0) = \frac{1 - e^{-\lambda}}{\lambda} > 0$$
  (e.g. at $\lambda = 1$, $\Delta f_0(0) = 1 - e^{-1} \approx 0.6321 \gt 0$). Strict negativity $\Delta f_0(k) \lt 0$ holds only for $k \ge 1$.
- **Resolution**: Lemma 4.4 (`Lem4_4`) itself is unaffected because at $k = 0$ with $0 \in A$, the positive term $\Delta f_0(0)$ attains the upper bound $(1 - e^{-\lambda})/\lambda$ while all $j \ge 1$ satisfy $\Delta f_j(0) \le 0$. Machine-checked refutation `not_Sec4_fwdDiff_f0_neg_printed` (`Formalization/Sweep/SweepC4.lean`) and corrected point-mass properties `Sec4_poissonSteinSol_pointMass_corrected` (`Sec4.lean` / `Sec4Proofs.lean`) are proved.

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
- **Proof-step pinpoint (`L2392-2398`)**: Under Reading (A), the proof step *"since each $X_i(\mathbf{Y})$ is an increasing or decreasing function applied to independent indicators, then so is $\phi \circ \mathbf{X}(\mathbf{Y})$"* (`L2395-2396`) fails directly: for $N = 2, n = 2$, $f_1(y_1, y_2) = y_1$, $f_2(y_1, y_2) = 1 - y_2$, and $\phi(x_1, x_2) = \mathbf{1}[x_1 \ge 1 \wedge x_2 \ge 1]$, $(\phi \circ \mathbf{f})(0, 0) = 0, (\phi \circ \mathbf{f})(1, 0) = 1, (\phi \circ \mathbf{f})(1, 1) = 0$ is neither increasing nor decreasing on $\{0, 1\}^2$ (`SteinMethod.not_thm4_17_comp_monotone_printed` / `SteinMethod.not_Thm4_17_comp_monotone_printed` in `Formalization/Sweep/SweepDMonotone.lean`), and at $N = 1, n = 2$ with $\phi(x_1, x_2) = \mathbf{1}[x_2 \ge 1]$, $\phi \circ \mathbf{f} = f_2$ has the opposite direction from $f_1$, violating FKG's same-direction hypothesis at `L2398`.
- **Resolution**: Formalize `Thm4_17_corrected`, `Thm4_17_implicit_coupling_corrected`, and `Thm4_17_comp_monotone_corrected` under Reading (B) (all $X_1, \ldots, X_n$ increasing, or all $X_1, \ldots, X_n$ decreasing on $\{0, 1\}^N$) together with the machine-checked refutations `SteinMethod.not_Thm4_17_printed` (`Formalization/PoissonSizeBias/Monotone/FKG.lean`) and `SteinMethod.not_Thm4_17_comp_monotone_printed` (`Formalization/Sweep/SweepDMonotone.lean`).

---

### `ISSUE-4.13` — Omitted Domain Guard $N \ge 2$ in Hypergeometric Variance and Total-Variation Bound (`SteinIntro.tex:2500-2505`)
- **Location**: Example 4.13 (`[Hypergeometric distribution]`, unlabeled, `SteinIntro.tex:2480-2505`; cross-referencing `ISSUE-TYPO-4.13` in Part I).
- **Issue**: Example 4.13 states $1 \le n \le N$ and $1 \le m \le N$, which allows $N = n = m = 1$. At $N = 1$, both the variance denominator $N^2 (N - 1)$ (`SteinIntro.tex:2500`) and every fraction $\frac{n}{N - 1}$, $\frac{m}{N - 1}$, $\frac{n m}{N(N - 1)}$, $\frac{1}{N - 1}$ in the displayed total-variation bound (`SteinIntro.tex:2504`) divide by $N - 1 = 0$ (whereas $W \equiv 1$ has $d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1)) = 1 - e^{-1} \gt 0$).
- **Formalization**: `Ex4_13_moments_corrected` (`SteinIntro.tex:2499-2501`, also correcting $(n - m)$ to $(N - m)$ per `ISSUE-TYPO-4.13`) and `Ex4_13_restricted` (`SteinIntro.tex:2480-2505`) add the domain guard $2 \le N$ (`Ex4_13_sizeBias` holds for all $1 \le n, m \le N$).

---

### `ISSUE-4.15` — Omitted Domain Guard $n \ge 2$ in Uniform Coupon-Collecting Bound `(4.13)` (`SteinIntro.tex:2526-2551`)
- **Location**: Example 4.15 (`[Coupon collecting]`, `\label{ex123}`, eq. `(4.13)` `\label{129}`, `SteinIntro.tex:2512-2551`).
- **Issue**: Example 4.15 specifies $n$ coupon types and $k$ boxes without stating $n \ge 2$. At $n = 1$, redirecting balls from box $1$ uniformly among the remaining $n - 1$ boxes (`SteinIntro.tex:2536-2538`) has empty target set, and the term $(1 - \frac{1}{n - 1})^k$ in `(4.13)` (`SteinIntro.tex:2550`) divides by $n - 1 = 0$.
- **Formalization**: `Ex4_15_restricted` (`SteinIntro.tex:2526-2551`, together with `Ex4_15_sizeBias` and `Ex4_15_asymptotic_ineq`) adds the domain guard $2 \le n$ (`Ex4_15_allTypes_iff` holds for all $n$).

---

### `ISSUE-4.16` — Omitted Zero-Denominator Guard $k \ne \log(\lambda)$ in Non-Uniform Coupon Collecting (`SteinIntro_utf8.tex:2590`)
- **Location**: Example 4.16 (`[Coupon collecting continued]`), `SteinIntro_utf8.tex` line 2590:
  `\dtv(W,Z)\leq \min\{1, \lambda\}\left[\max_{i}(1-p_i)^k+\frac{k}{\lambda}\left(\frac{\lambda \log(k)}{k-\log(\lambda)}+\frac{4}{k}\right)^2\right].`
- **Issue**: The displayed upper bound divides by $k - \log(\lambda)$ without stating
  $k \ne \log(\lambda)$. This zero denominator occurs on the non-degenerate interior of the
  probability simplex: at $k = 2$ and $n = 9$, $\lambda(p) = \sum_{i=1}^9 (1 - p_i)^2$ equals
  $64/9 \lt e^2$ at $p = (1/9, \dots, 1/9)$ and $2273/288 \gt e^2$ at
  $p = (17/18, 1/144, \dots, 1/144)$, so
  by continuity there exist $p_1, \dots, p_9 \gt 0$ with $\sum_{i=1}^9 p_i = 1$ and
  $\lambda = e^2 \gt 0$, where $k - \log(\lambda) = 0$. (`1 ≤ k` and `0 < \lambda` are domain guards
  for `4/k`, `\log(k)`, `k/\lambda`, `\log(\lambda)`, and `\Po(\lambda)`.)
- **Formalization**: Singularity witness proved in `Ex4_16_exists_zero_denom`
  (`ex4_16_exists_zero_denom`); the printed bound is true wherever defined (not a source error in
  the inequality) and is proved from scratch for all $1 \le k$, $\lambda \gt 0$, and
  $k \ne \log(\lambda)$ (covering both $\log(\lambda) \lt k$ and $k \lt \log(\lambda)$) in
  `Ex4_16_restricted` (`ex4_16_restricted`).

---

### `ISSUE-REM-4.17` — False Theorem 4.14 (`\ref{thm122}`) Claim for Boxes Containing At Least $m \ge 1$ Balls (`SteinIntro_utf8.tex:2600`)
- **Location**: Remark 4.17, `SteinIntro_utf8.tex` line 2600:
  `Finally, could also consider the number of boxes containing exactly $m\geq0$ balls and containing at least $m\geq1$ balls, Theorem \ref{thm122} applies to the latter problem.  See Chapter 6 of \cite{bhj92}.`
- **Issue**: Theorem 4.14 (`\ref{thm122}`) requires an *increasing* conditional coupling
  $X_j^{(i)} \ge X_j$ ($j \ne i$) and gives the upper bound
  $\min\{1, \lambda^{-1}\}(\mathrm{Var}(W) - \lambda + 2 \sum_{i=1}^n q_i^2)$. For fixed ball
  count $k$ and indicators $X_i = \mathbf{1}[B_i \ge m]$ ($m \ge 1$), conditioning on $X_i = 1$
  absorbs at least $m$ balls into box $i$, leaving fewer balls for boxes $j \ne i$ and making the
  indicators **negatively** related ($X_j^{(i)} \le X_j$). At $n = 2, k = 1, m = 1,
  p = (1/2, 1/2)$, $W \equiv 1$ has $\lambda = 1$, $\mathrm{Var}(W) = 0$, and
  $q_1 = q_2 = 1/2$, so no coupling satisfies $X_2^{(1)} \ge X_2$ a.s. and Theorem 4.14's bound
  evaluates to $0 \lt e^{-1} \le d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1))$ (and to $-1/3 \lt 0$ at
  $n = 3, k = 1, m = 1, p = (1/3, 1/3, 1/3)$, where $W \equiv 1$, $\lambda = 1$,
  $\mathrm{Var}(W) = 0$, and $\sum_{i=1}^3 q_i^2 = 1/3$). The theorem that actually applies is
  **Theorem 4.19 (`\ref{thm125}`)**.
- **Formalization**: Refuted as printed by `not_Rem4_17_atLeast_printed`
  (`not_rem4_17_atLeast_printed`), and proved with the decreasing conditional coupling and Theorem
  4.19 bound in `Rem4_17_atLeast_corrected` (`rem4_17_atLeast_corrected`).

---

### `ISSUE-5.2-ODE` — Non-Differentiability at Jump Discontinuities in Lemma 5.2
- **Source**: Lemma 5.2 (`\label{lem172}`, `SteinIntro.tex:2740-2745`, proof `2774-2779`)
- **Printed text (verbatim, `L2740-2745`)**:
  ```tex
  \begin{lemma}\label{lem172}
  Let $Z\sim\Exp(1)$ and for some function $h$ let $f_h$ be the unique solution of
  \ban
  f_h'(x)-f_h(x)=h(x)-\IE[h(Z)] \label{171}
  \ee
  such that $f_h(0)=0$. 
  ```
- **Counterexample (`not_exists_hasDerivAt_expStein_Iic`)**: Exactly as in `ISSUE-2.2`, for discontinuous bounded non-negative $h$ such as the half-line indicator $h = \mathbf{1}_{(-\infty, 1]}$ used in Kolmogorov bounds, Darboux's theorem precludes any everywhere two-sided differentiable solution $g : \mathbb{R} \to \mathbb{R}$ of $g'(x) - g(x) = h(x) - \mathbb{E}[h(Z)]$: any such $g$ would be continuous, hence $g'(x) = g(x) + h(x) - \mathbb{E}[h(Z)]$ would have a jump discontinuity of size $1$ at $x = 1$, contradicting the intermediate value property for derivatives (machine-checked as `not_exists_hasDerivAt_expStein_Iic` in `Formalization/Exponential/SteinEquation.lean`).
- **Resolution**: Formalize `Lem5_2_formula` (interval-integral formula and boundary value $f_h(0) = 0$ for locally integrable $h \in L^1(\mathrm{Exp}(1))$, plus two-sided ODE and uniqueness from $g(0) = 0$ alone when $h$ is continuous), `Lem5_2_ode_contAt` (two-sided ODE at every continuity point of $h$), `Lem5_2_ode_ae` (local absolute continuity, Lebesgue-a.e. two-sided ODE, and uniqueness among locally AC functions with $g(0) = 0$), and `Lem5_2_1` with `LipschitzWith (Real.toNNReal (2 * M)) (expSteinSol h)` alongside the pointwise `deriv` and `derivWithin` bounds.

---

### `ISSUE-5.5` — Equilibrium Uniqueness and Lebesgue Absolute Continuity Fail at $\mu = \mathbb{E}[W] = 0$
- **Source**: Definition 5.2 and following prose (`SteinIntro.tex:2836-2845`)
- **Printed text (verbatim, `L2836-2845`)**:
  ```tex
  \begin{definition}
  Let $W\geq0$  a random variable with $\IE[W]=\mu$.  We say that $W^e$ has the \emph{equilibrium} distribution
  with respect to $W$ if 
  \ban
  \IE[f(W)]-f(0)=\mu\IE[f'(W^e)] \label{173}
  \ee
  for all Lipschitz functions $f$.  
  \end{definition}
  We will see below that the equilibrium distribution is absolutely continuous with respect to Lebesgue measure, so that the
  right hand side of \eq{173} is well defined.  Before this discussion, we note
  ```
- **Counterexample**: Definition 5.2 allows $\mu = \mathbb{E}[W] = 0$ ($W = 0$ almost surely), under which `IsEquilibrium` is formalized literally (`D1`) and Proposition 5.5 (`Prop5_5`) holds literally with no restriction. However, at $\mu = 0$ equation `(5.3)` reduces to $0 = 0 \cdot \mathbb{E}[f'(W^e)]$, which is satisfied by **every** random variable $W^e$ — in particular $W^e \equiv 0$ ($\mathrm{Law}(W^e) = \delta_0$), which is neither unique nor absolutely continuous with respect to Lebesgue measure.
- **Resolution**: Keep `IsEquilibrium` and `Prop5_5` literal without restricting $\mu \gt 0$, and include the explicit positivity hypothesis `0 < ∫ ω, W ω ∂P` on the uniqueness and Lebesgue-density statement `Sec5_1_equilibrium_ac`.

---

### `ISSUE-5.4` — Equilibrium Scaling $(cX)^e \stackrel{d}{=} c X^e$ Requires $c \gt 0$
- **Source**: Example 5.4 (`\label{ex171}`, `SteinIntro.tex:2894-2895`) and Proof of Theorem 5.9 (`SteinIntro.tex:3023-3024`)
- **Printed text (verbatim, `L2894-2895` and `L3023-3024`)**:
```tex
It is easy to verify that for a constant $c$ and a non-negative variable $X$, $(cX)^e\ed cX^e$, so that if we define $W=pN$ 
our remarks above imply that $W^e:=W-pU$ has the equilibrium distribution with respect to $W$.
```
```tex
$\IE\abs{Y_n-Y_n^e}\leq C \log(n)$.  Once this is established, the result is proved 
by Theorem \ref{thm172} and the fact that $(cY_n)^e\ed cY_n^e$ for any constant $c$.
```
- **Counterexample**: For $c \lt 0$ and $\mathbb{P}(X \gt 0) \gt 0$, $c X$ violates the non-negativity requirement of Definition 5.2; for $c = 0$ and $X \sim \mathrm{Exp}(1)$ ($X^e \sim \mathrm{Exp}(1)$, $0 \cdot X^e \equiv 0$), $0 \cdot X \equiv 0$ has mean $\mu = 0$, so by `ISSUE-5.5` any variable $Y$ (e.g. $Y \equiv 1 \not\stackrel{d}{=} 0 \cdot X^e$) satisfies `(5.3)` for $0 \cdot X$.
- **Resolution**: Formalize `Sec5_1_equilibrium_scale_restricted` under `0 < c` (`sec5_1_equilibrium_scale_restricted` in `Formalization/Exponential/Equilibrium.lean`).

---

### `ISSUE-5.7` — Unstated Support $M \ge 1$ and Joint Independence of $(N, M)$ from $(X_i)$ in Theorem 5.7
- **Source**: Theorem 5.7 (`\label{thm1710}`, `SteinIntro.tex:2915-2929`)
- **Printed text (verbatim, `L2916-2928`)**:
  *"Let $X_1, X_2, \ldots$ be square integrable, non-negative, and independent random variables with $\mathbb{E}[X_i]=1$. Let $N \gt 0$ be an integer valued random variable with $\mathbb{E}[N]=1/p$ for some $0 \lt p\leq 1$ and let $M$ be defined on the same space as $N$ such that $\mathbb{P}(M=m)=p \mathbb{P}(N\geq m)$. If $W=p\sum_{i=1}^N X_i$, $Z\sim\mathrm{Exp}(1)$, and $X_i^e$ is an equilibrium coupling of $X_i$ independent of $N, M$, and $(X_j)_{j\not=i}$, then $d_{\mathrm{W}}(W, Z)\leq 2p\left(\mathbb{E}|X_M-X_M^e|+\mathbb{E}|N-M|\right) \leq 2p\left(1+\frac{\mu_2}{2}+\mathbb{E}|N-M|\right)$, where $\mu_2:=\sup_{i} \mathbb{E}[X_i^2]$."*
- **Issues & Counterexamples (`not_Thm5_7_printed`)**:
  1. *Omitted $m \ge 1$ restriction in `L2920`*: Because $N \gt 0$ is integer-valued with $\mathbb{E}[N] = 1/p$, $\sum_{m=1}^\infty p \mathbb{P}(N \ge m) = p \mathbb{E}[N] = 1$. However, `L2920` prints $\mathbb{P}(M = m) = p \mathbb{P}(N \ge m)$ without restricting $m \ge 1$; for every integer $m \le 0$, $\mathbb{P}(N \ge m) = 1$, which would assign mass $p \gt 0$ to infinitely many $m \le 0$ (and $X_M$ at `L2925` is only indexed for $M \ge 1$). Thus $M$ must take values in $\{1, 2, \ldots\}$ with $\mathbb{P}(M = m) = p \mathbb{P}(N \ge m)$ for $m \ge 1$ (matching Remark 5.5 at `L2935`).
  2. *Omitted independence of $(N, M)$ from $(X_i)_{i \ge 1}$*: `L2916-2922` omits that $(N, M)$ is independent of $(X_i)_{i \ge 1}$ (unlike Theorem 5.6 at `L2906-2907`). Machine-checked counterexample (`SteinMethod.not_Thm5_7_printed` in `Formalization/Exponential/GeometricSumsCounterexample.lean`): fix odd $m = 4001$, set $p = 1 - 2^{-1/4001} \in (0, 1)$ so $(1 - p)^{4001} = 1/2$ and $\mathbb{P}(G \le 4001) = 1/2$ for $G \sim \mathrm{Ge}(p)$, let $X_i \stackrel{\text{i.i.d.}}{\sim} 2\,\mathrm{Bernoulli}(1/2)$ ($\mathbb{E}[X_i] = 1$, $\mu_2 = 2$), let $X_i^e \stackrel{\text{i.i.d.}}{\sim} \mathrm{Unif}(0, 2)$ completely independent of $(X_j)_{j \ge 1}$ and $(N, M)$, and sample $N = M$ from $\mathcal{L}(G \mid G \gt 4001)$ on $\{S_{4001} \gt 0\}$ and from $\mathcal{L}(G \mid G \le 4001)$ on $\{S_{4001} \lt 0\}$ where $S_{4001} := \sum_{i=1}^{4001} (X_i - 1)$. Conditioning on $(S_{4001}, N)$ gives the exact identity
     $$\mathbb{E}[W] - 1 = \frac{p}{2}\,\mathbb{E}|S_{4001}|\left(1 - \frac{\mathbb{E}[G \mid G \le 4001]}{4001}\right).$$
     Since $\mathbb{E}|S_{4001}| \gt 36$ (fourth-moment / Hölder bound) and $\mathbb{E}[G \mid G \le 4001] \le 2001$ (monotone pairing $k \leftrightarrow 4002 - k$), $d_{\mathrm{W}}(W, Z) \ge \mathbb{E}[W] - 1 \gt \frac{p}{2} \cdot 36 \cdot \frac{2000}{4001} \gt 8 p \gt 4 p = 2 p(1 + \mu_2 / 2 + \mathbb{E}|N - M|)$.
- **Resolution**: Formalize `Thm5_7_corrected` (`SteinMethod.thm5_7_corrected_minimal`) under the exact minimal hypotheses: $M \ge 1$ a.s. with $\mathbb{P}(M = m) = p \mathbb{P}(N \ge m)$ for $m \ge 1$, the printed joint independence of each $X_i^e$ from $(N, M, (X_j)_{j \ne i})$, and the single omitted joint independence $(N, M) \perp (X_i)_{i \ge 1}$ (matching `SteinMethod.not_Thm5_7_printed` in every other clause; see also [`docs/DEFINITIONS.md`](DEFINITIONS.md) §5.3).

---

### `ISSUE-5.8` — Ill-Defined Division by $\sigma^2 = 0$ When $Z_1 \equiv 1$ in Theorem 5.8 and Kolmogorov's Survival Limit
- **Source**: Theorem 5.8 (Yaglom's Theorem, `SteinIntro.tex:3007-3013`) and Kolmogorov's survival asymptotic (`SteinIntro.tex:3028, 3185-3186`)
- **Printed text (verbatim, `L3007-3013` and `L3185-3186`)**:
  ```tex
\begin{theorem}[Yaglom's Theorem]
Let $1=Z_0, Z_1,\ldots$ be the generation sizes of a Galton-Watson branching process where
$\IE[Z_1]=1$ and $\var(Z_1)=\sigma^2<\infty$.  If $Y_n\ed (Z_n|Z_n>0)$ and $Z\sim \Exp(1)$, then
\ba
\lim_{n\to\infty}\dk\left(\frac{2Y_n}{n\sigma^2}, Z\right)=0.
\ee
\end{theorem}
  ```
  ```tex
Using Kolmogorov's estimate (see Chapter 1, Section 9 of \cite{atne72}),
we have $\lim_{n\to\infty}n\IP(Z_n>0) = 2/\sigma^2$, which
  ```
- **Boundary Defect (`not_Thm5_8_printed`)**: Theorem 5.8 assumes $\mathbb{E}[Z_1] = 1$ and $\mathrm{Var}(Z_1) = \sigma^2 \lt \infty$ without requiring $\sigma^2 \gt 0$. For the deterministic critical branching process $Z_1 \equiv 1$ ($\sigma^2 = 0$), $Z_n \equiv 1$ and $Y_n \equiv 1$ for all $n \ge 0$, so the printed expressions $\frac{2 Y_n}{n \sigma^2}$ and $\frac{2}{\sigma^2}$ are mathematically ill-defined (division by $0$, not false when $\sigma^2 \gt 0$), while $n \mathbb{P}(Z_n \gt 0) = n \to \infty$. Under Lean's `x / 0 = 0` convention, $\mathcal{L}(2 Y_n / (n \sigma^2)) = \delta_0$ and $d_{\mathrm{K}}(\delta_0, \mathrm{Exp}(1)) = 1 \not\to 0$ (machine-checked as `SteinMethod.not_Thm5_8_printed` in `Formalization/Branching/YaglomRate.lean`).
- **Resolution**: Formalize `Thm5_8_restricted` (`thm5_8_restricted`) and `Sec5_3_kolmogorov_survival_restricted` (`sec5_3_kolmogorov_survival_restricted`) under the explicit positivity hypothesis `0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P`.

---

### `ISSUE-5.9` — Boundary Failure at $n = 1$ ($\log 1 = 0$) in Theorem 5.9 and the $\log(n)$ Coupling Bound (`L3023`, `L3141`)
- **Source**: Theorem 5.9 (`SteinIntro.tex:3015-3020`) and the logarithmic coupling bound (`SteinIntro.tex:3022-3023, 3140-3141`)
- **Printed text (verbatim, `L3015-3023`)**:
  ```tex
\begin{theorem}
Let $Z_0, Z_1, \ldots$ as in Yaglom's Theorem above and assume also that $\IE\abs{Z_1}^3<\infty$.  If $Y_n\ed (Z_n|Z_n>0)$ and $Z\sim \Exp(1)$, then for some constant $C$, 
\ba
\dw\left(\frac{2Y_n}{n\sigma^2}, Z\right)\leq C\frac{\log(n)}{n}.
\ee
\end{theorem}
\begin{proof}
We will construct a copy of $Y_n$ and $Y_n^e$ having the equilibrium distribution on the same space and then show that
$\IE\abs{Y_n-Y_n^e}\leq C \log(n)$.  Once this is established, the result is proved 
  ```
- **Counterexample (`not_Thm5_9_printed`)**:
  1. *Theorem 5.9 at $n = 1$ with $\sigma^2 \gt 0$*: Take $\mathbb{P}(Z_1 = 0) = \mathbb{P}(Z_1 = 2) = 1/2$ (`Sec5_3_exists_isGaltonWatson_pos_var`), so $\mathbb{E}[Z_1] = 1$, $\sigma^2 = 1 \gt 0$, and $\mathbb{E}|Z_1|^3 = 4 \lt \infty$. At $n = 1$, $Y_1 = (Z_1 \mid Z_1 \gt 0) = 2$ a.s., so $\frac{2 Y_1}{1 \cdot \sigma^2} = 4$ a.s. and $d_{\mathrm{W}}(\delta_4, \mathrm{Exp}(1)) \ge |4 - 1| = 3 \gt 0$, whereas for **every** constant $C \in \mathbb{R}$, $C \frac{\log(1)}{1} = 0$. Machine-checked as `SteinMethod.not_Thm5_9_printed` in `Formalization/Branching/YaglomRate.lean` (in addition, $\sigma^2 = 0$ is ill-defined as in `ISSUE-5.8`).
  2. *Coupling discrepancy $\mathbb{E}|Y_n - Y_n^e| \le C \log(n)$ at $n = 1$ (`L3023`, `L3141`)*: At $n = 1$, $Y_1 - Y_1^e = U + (R_{1,1}' - R_{1,1})\mathbf{1}_{L_{1,1} \gt 0} \in U + \mathbb{Z}$ with $U \sim \mathrm{Unif}(0, 1)$, so $|Y_1 - Y_1^e| \ge \min(U, 1 - U)$ and $\mathbb{E}|Y_1 - Y_1^e| \ge 1/4 \gt 0 = C \log(1)$ for every $C \in \mathbb{R}$ and every critical offspring law.
- **Resolution**: Formalize `Thm5_9_restricted` (`thm5_9_restricted`, restricted to $\sigma^2 \gt 0$ and $n \ge 2$) and `Sec5_3_lpp_mean_diff_log_restricted` (`sec5_3_lpp_mean_diff_log_restricted`, restricted to $n \ge 2$ without needing $\sigma^2 \gt 0$).

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
- **Counterexample (`not_Sec6_opening_wasserstein_printed`)**: Take $p = 1/4$ and $W \equiv 4$ deterministically ($W \gt 0$ integer-valued with $\mathbb{E}[W] = 4 = 1/p$). Then $p W \equiv 1$, $d_{\mathrm{W}}(\delta_1, \mathrm{Exp}(1)) = 2 e^{-1} \lt 1$, whereas $X \sim \mathrm{Ge}(1/4)$ on $\{1, 2, \dots\}$ satisfies $d_{\mathrm{W}}(X, 4) = \mathbb{E}|X - 4| = 2 \cdot \frac{81}{64} = \frac{81}{32}$, so $|d_{\mathrm{W}}(pW, Z) - d_{\mathrm{W}}(X, W)| = \frac{81}{32} - 2 e^{-1} \approx 1.80 \gt \frac{1}{4} = p$.
- **Cause & Resolution**: By homogeneity of Wasserstein distance, $d_{\mathrm{W}}(p X, p W) = p\,d_{\mathrm{W}}(X, W)$, so the reverse triangle inequality combined with Example 5.4 ($d_{\mathrm{W}}(p X, Z) \le p$) yields $|d_{\mathrm{W}}(p W, Z) - p\,d_{\mathrm{W}}(X, W)| \le d_{\mathrm{W}}(p X, Z) \le p$. Machine-checked refutation `not_Sec6_opening_wasserstein_printed` (`not_opening_wasserstein_printed`), reduction `opening_wasserstein_of_ex5_4`, and unconditional corrected theorem `Sec6_opening_wasserstein_corrected` (`Sec6_opening_wasserstein_corrected_holds` / `opening_wasserstein_corrected`, importing `wassersteinDist_shiftedGeomLaw_le` from `Formalization/Exponential/GeometricExample.lean`) are proved in `Formalization/Geometric/OpeningBound.lean`.

---

### `ISSUE-6.4` — Boundary Degeneracy at $p = 1$ ($W \equiv 0$) for Discrete Equilibrium Uniqueness and Renewal Tail Formula
- **Source**: Preamble to Proposition 6.4 (`SteinIntro.tex:3290-3291`) and Remark 6.2 (`\label{rem175}`, `SteinIntro.tex:3304-3310`)
- **Printed text (verbatim)**:
  ```tex
  The following result provides a constructive definition of the discrete equilibrium distribution, so that the
  right hand side of \eq{1717} defines a probability distribution.
  \begin{proposition}\label{prop172}
  Let $W\geq0$ be an integer-valued random variable with $\IE[W]=(1-p)/p$ for some $0<p\leq 1$ and let $W^s$ have the size-bias distribution
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

### `ISSUE-EX7.2` — Lower-Order Claim $e^{-t\log(t)}$ Fails for $0 \lt \lambda \le e^{-1}$ in Example 7.2
- **Source**: Example 7.2 (`\label{ex212}`, `SteinIntro.tex:3447-3461`)
- **Printed text (verbatim, `L3447-3461`)**:
  ```tex
  \begin{example}[Poisson distribution]\label{ex212}
  Let $Z$ have the Poisson distribution with mean $\lambda$.  
  A simple calculation implies $\IE[e^{\theta Z}]=\exp\{\lambda(e^\theta-1)\}$ for all $\theta \in \IR$,
  so that for $\theta, t>0$ Proposition \ref{prop211} implies
  \ba
  \IP(Z-\lambda\geq t)\leq  \exp\{\lambda(e^\theta-1)-\theta(t+\lambda)\},
  \ee
  and choosing the minimizer $\theta=\log(1+t/\lambda)$ yields 
  \ba
  \IP(Z-\lambda \geq t)\leq  \exp\left\{ -t\left(\log\left(1+\frac{t}{\lambda}\right)-1\right) -\lambda\log\left(1+\frac{t}{\lambda}\right) \right\},
  \ee
  which is of smaller order than $e^{-ct}$ for $t$ large and fixed $c>0$, but of bigger order than $e^{-t\log(t)}$.
  This is the best behavior we can hope for using Proposition \ref{prop211} in examples
  where the random variable is approximately Poisson (such as sums of independent indicators, each with a small probability of being one). 
  \end{example}
  ```
- **Counterexample (`poisson_bound_order_not_tendsto_of_le` / `not_poisson_bound_order_printed`)**: Writing $B(\lambda, t) := \exp\bigl(-t(\log(1 + t/\lambda) - 1) - \lambda\log(1 + t/\lambda)\bigr)$, we have $\log B(\lambda, t) + t\log t = (1 + \log\lambda)t - \lambda\log t + O(1)$ as $t \to \infty$. Hence $\lim_{t \to \infty} e^{-t\log t} / B(\lambda, t) = 0$ holds if and only if $\lambda \gt e^{-1}$: for **every** $\lambda \in (0, e^{-1}]$, $e^{-t\log t} / B(\lambda, t) \ge 1$ for all $t \ge 1$ (machine-checked for all $\lambda \in (0, e^{-1}]$ as `poisson_bound_order_not_tendsto_of_le` in `Formalization/Concentration/Followups.lean` and at $\lambda = e^{-1}$ as `not_poisson_bound_order_printed` in `Formalization/Concentration/Basic.lean`; e.g., at $\lambda = 0.1, t = 100$, $\log B \approx -591.57 \lt -460.52 = -100\log 100$).
- **Resolution**: Formalize `Ex7_2` (MGF, Chernoff bound, minimizer optimality at $\theta = \log(1 + t/\lambda)$, and $B(\lambda, t) = o(e^{-c t})$ for every $c \gt 0$), `Ex7_2_order_corrected` ($e^{-c t \log t} / B(\lambda, t) \to 0$ for all $\lambda \gt 0$ and $c \gt 1$), `Ex7_2_order_restricted` ($e^{-t\log t} / B(\lambda, t) \to 0$ for $\lambda \gt e^{-1}$), and `poisson_bound_order_not_tendsto_of_le` / `not_poisson_bound_order_printed`.

---

### `ISSUE-EX7.4` — Centered vs. Uncentered Sum Symbol Clash (`W` and `\mu := \mathbb{E}[W]`) in Example 7.4(2)
- **Source**: Example 7.4 (`SteinIntro.tex:3497-3502` and `3516-3536`, eq. `(7.2)` `\label{21198}`)
- **Printed text (verbatim, `L3497-3502` and `L3516-3536`)**:
  ```tex
  \begin{example}[Sum of independent variables]
  Let $X_1, \ldots, X_n$ be independent random variables with $\mu_i:=\IE[X_i]$, $\sigma_i^2:=\var(X_i)<\infty$
  and define $W=\sum_i X_i-\mu_i$.
  Let $X_1', \ldots, X_n'$ be an independent copy of the $X_i$ and for $I$ independent of all else and uniform on $\{1, \ldots, n\}$,
  let $W'=W-X_I+X_I'$ so that as usual, $(W, W')$ is a $1/n$-Stein pair.  We consider two special cases of this setup.
  \begin{enumerate}
  ```
  ```tex
  \item For $i=1, \ldots, n$, assume  $0\leq X_i \leq 1$. Then the moment generating function condition of the theorem is satisfied and
  \ba
  \IE[(W'-W)^2 | (X_j)_{j\geq 1}]&=\frac{1}{n}\sum_{i=1}^n\IE[(X_i'-X_i)^2 | (X_j)_{j\geq 1}] \\
  	&=\frac{1}{n}\sum_{i=1}^n\IE[(X_i')^2]-2\mu_iX_i+X_i^2  \\
  	&\leq \frac{1}{n}\sum_{i=1}^n\mu_i +X_i= \frac{1}{n}(2\mu+W),
  \ee
  where $\mu:=\IE[W]$ and we have used that $-2\mu_iX_i\leq 0$ and $X_i^2\leq X_i$.
  We can now apply Theorem \ref{thm211a} with $B=1/2$ and $C=\mu$ to find that
  for $t>0$,
  \ban
  \IP\left(\abs{W-\mu}\geq t\right)\leq 2\exp\left\{-\frac{t^2}{2\mu+t}\right\}. \label{21198}
  \ee
  Note that if $\mu$ is constant in $n$, then \eq{21198} is of the order $e^{-t}$ for large $t$, which according to Example \ref{ex212} is
  similar to the order of Poisson tails.  However, if $\mu$ and $\sigma^2:=\var(W)$ are both going to infinity at the same rate,
  then \eq{21198} implies
  \ba
  \IP\left(\frac{\abs{W-\mu}}{\sigma}\geq t\right)\leq 2\exp\left\{-\frac{t^2}{2\frac{\mu}{\sigma^2}+\frac{t}{\sigma}}\right\}, 
  \ee
  so that for $\sigma^2$ large, the tails are of order $e^{-ct^2}$, which according to Example \ref{ex211} is
  similar to the order of Gaussian tails.
  \end{enumerate} 
  ```
- **Counterexample under literal `L3499` + `L3522`**: Line `3499` defines $W = \sum_i (X_i - \mu_i)$ (so $\mathbb{E}[W] = 0$), whereas Example 7.4(2) writes $\frac{1}{n}\sum_{i=1}^n \mu_i + X_i = \frac{1}{n}(2\mu + W)$ (`L3520`) with *"where $\mu := \mathbb{E}[W]$"* (`L3522`) and claims $\mathbb{P}(|W - \mu| \ge t) \le 2\exp(-t^2/(2\mu + t))$ (`(7.2)`, `L3526`). Under $\mu = \mathbb{E}[W] = 0$, `(7.2)` asserts $\mathbb{P}(|W| \ge t) \le 2 e^{-t}$, which fails at $n = 16$ i.i.d. $\mathrm{Bernoulli}(1/2)$ summands and $t = 2$: $\mathbb{P}(|\sum_{i=1}^{16} (X_i - 1/2)| \ge 2) = 29786 / 65536 \approx 0.4545 \gt 0.2707 \approx 2 e^{-2}$. (Also `L3532` divides by $\sigma = \sqrt{\mathrm{Var}(W)}$, which requires $\mathrm{Var} \gt 0$.)
- **Resolution**: Formalize `Ex7_4_2_corrected` using the uncentered sum $S = \sum_{i=1}^n X_i$ and $\mu = \mathbb{E}[S] = \sum_{i=1}^n \mu_i$ (so $W = S - \mu$ satisfies $\sum_i (\mu_i + X_i) = 2\mu + W$), guarding the standardized display `L3532` by `0 < variance S P`, plus `Ex7_4_2_order` (`L3528`: $\exp(-t^2/(2\mu + t)) / e^{-t} \to e^{2\mu}$ as $t \to \infty$ for constant $\mu \ge 0$).

---

### `ISSUE-7.5` — Stein Parameter $a = 2/(n - 1)$ Violates $a \le 1$ at $n = 2$ (and Divides by Zero at $n = 1$)
- **Source**: Example 7.5 and Proposition 7.3 (`SteinIntro.tex:3597-3625`)
- **Printed text**: For a uniform random permutation $\sigma$ of $\{1, \dots, n\}$ and uniform random transposition $\tau$, claims (`L3610`, `L3619`) that $(W, W')$ is a $\frac{2}{n - 1}$-Stein pair and applies Theorem 7.2 (`\label{thm211a}`).
- **Counterexample**: At $n = 2$ with $a_{11} = a_{22} = 1$ and $a_{12} = a_{21} = 0$, $W = \pm 1$ with equal probability and the unique transposition $\tau = (1\,2)$ gives $W' = -W$, so $\mathbb{E}[W' \mid W] = -W = (1 - 2)W$. Here $a = \frac{2}{2 - 1} = 2 > 1$, which violates Definition 3.2's requirement $0 < a \le 1$ (`L954`). Furthermore, at $n = 1$ no transposition exists and $2/(n - 1)$ divides by zero (though $W \equiv 0$ makes Proposition 7.3's inequality $\mathbb{P}(|W| \ge t) = 0 \le 2 e^{\dots}$ trivially true for $t > 0$).
- **Resolution (`D7`)**: Keep `0 < a ∧ a ≤ 1` in `IsSteinPair` as printed, prove the library concentration theorem (Theorem 7.2) for any `0 < a`, formalize `Ex7_5_steinPair_restricted` for all `2 ≤ n` (giving $\mathbb{E}[W] = 0$, exchangeability, $\mathbb{E}[W' \mid W] = (1 - \frac{2}{n - 1})W$, and `3 ≤ n → IsSteinPair …`, differing from the printed claim only by dropping Def 3.2's $a \le 1$ at $n = 2$) together with the machine-checked refutation `not_combinatorial_isSteinPair_n2` (`Formalization/Concentration/CombinatorialPair.lean`), and use the `0 < a` library bound directly to prove `Prop7_3` for all $n \in \mathbb{N}$.

---

### `ISSUE-7.6` — Missing $t \ge 0$ Hypothesis in Size-Bias Concentration Theorem 7.6
- **Source**: Theorem 7.6 (`\label{thm211c}`, `SteinIntro.tex:3814-3826`)
- **Printed text**: States tail bounds $\mathbb{P}(\frac{X - \mu}{\sigma} \le -t) \le \exp(\frac{-t^2}{2 C \mu / \sigma^2})$ and $\mathbb{P}(\frac{X - \mu}{\sigma} \ge t) \le \exp(\frac{-t^2}{2(C \mu/\sigma^2 + C t/(2\sigma))})$ without stating $t \ge 0$ (unlike Proposition 7.1 `L3413` and Theorem 7.2 `L3485`, which print *"for all $t \gt 0$"*).
- **Counterexample**: Take $X \sim \mathrm{Bernoulli}(1/2)$ and $X^s \equiv 1 \ge X$ ($C = 1$, $\mu = 1/2$, $\sigma = 1/2$). At $t = -3 < 0$, $\mathbb{P}((X - \mu)/\sigma \le -(-3)) = \mathbb{P}(2X - 1 \le 3) = 1$, whereas $\exp(-(-3)^2 / (2 \cdot 2)) = e^{-9/4} < 1$.
- **Resolution**: Formalize `Thm7_6_corrected` quantifying `∀ t : ℝ, 0 ≤ t → ...` together with the machine-checked refutation `not_sizeBias_tail_bounds_printed` in `Formalization/Concentration/SizeBias.lean` (note `0 < C` follows automatically from `0 < Var(X)` and `|X - X^s| ≤ C`).

---

### `ISSUE-EX7.6` — Missing Factor `2` in Variance Formula (Plus Wrap-Around Conditions on $n$, Degenerate $p \in \{0, 1\}$, and Omitted $t \ge 0$) in Example 7.6
- **Source**: Example 7.6 (`SteinIntro.tex:3878-3884`)
- **Printed text (verbatim, `L3878-3884`)**:
  ```tex
  \begin{example} 
  Let $Y_1,\dots, Y_n$ be i.i.d.\! $Be(p)$, fix $k\geq 1$, and define $X_i = \prod_{j=i}^{i+k-1} Y_j$ with the bounds being modular.  Further define $X=\sum_{i=1}^n X_i$ and define $X^s$ by sampling $X_1,\dots, X_n$ and forcing $X_1=1$.  Conditional on this, the rest of the $Y_i$ are as before.  If 
  \[ X^{(k)}_i = \begin{cases} 1 & \textrm{if there exists a head run of length $k$ at $i$ after forcing} \\ 0 & \textrm{otherwise},\end{cases}\]
  then $X^s = 1+\sum_{j=2}^n X^{(k)}_j$.  Note that $X^s\geq X$ and $|X^s-X|\leq 2k-1$.  In this case Theorem \ref{thm211c} implies
  \[ \IP\left(\left|\frac{X-\mu}{\sigma}\right| \geq t\right) \leq 2 \exp\left( \frac{-t^2}{2(2k-1)\left(\frac{\mu}{\sigma^2} + \frac{t}{2\sigma} \right)}\right),\]
  where $\mu = np^k$ and $\sigma^2 = \mu\left(1-p^k+\sum_{i=1}^{k-1} (p^i-p^k)\right)$.
  \end{example}
  ```
- **Issues & Counterexamples**:
  1. *Missing factor `2` in $\sigma^2$ (`L3883`)*: For $n \ge 2k - 1$, each cyclic window $X_i$ overlaps **two** translates $X_{i+r}$ and $X_{i-r}$ ($\bmod\,n$) at each lag $r \in \{1, \dots, k - 1\}$, each contributing covariance $p^k(p^r - p^k)$, so $\mathrm{Var}(X) = \mu\bigl(1 - p^k + 2\sum_{r=1}^{k-1}(p^r - p^k)\bigr)$. Machine-checked counterexample (`Ex7_6_variance_counterexample` in `Formalization/Concentration/CircularRuns.lean`): for $n = 4$, $k = 2$, $p = 1/2$, $\mu = 1$ and $\mathrm{Var}(X) = 5/4$, whereas the printed formula evaluates to $1 \ne 5/4$.
  2. *Wrap-around when $n \lt 2k - 1$*: $\mu = n p^k$ requires $n \ge k$ (at $n = 1, k = 2, p = 1/2$, $X = Y_1^2 = Y_1$ has $\mathbb{E}[X] = 1/2 \ne 1/4$), and the lag-covariance sum requires $n \ge 2k - 1$ (at $n = 2, k = 2, p = 1/2$, $X = 2 Y_1 Y_2$ has $\mathrm{Var}(X) = 3/4 \ne 5/8$). However, the size-bias coupling (`IsSizeBias P X P Xs`), monotonicity (`X ≤ᵐ[P] Xs`), bounded increment (`|Xs - X| ≤ 2k - 1` a.s.), variance positivity (`0 < Var(X)` for $0 \lt p \lt 1$), and the two-sided tail bound hold for **all** $n \ge 1, k \ge 1, 0 \lt p \lt 1, t \ge 0$.
  3. *Degenerate $p \in \{0, 1\}$ and $t \lt 0$*: At $p \in \{0, 1\}$, $\sigma = 0$; at $t \lt 0$, the tail bound fails just as in `ISSUE-7.6`.
- **Resolution**: Formalize `Ex7_6_corrected` assuming $1 \le n$, $1 \le k$, $0 \lt p \lt 1$, proving the coupling properties and two-sided concentration bound for $t \ge 0$ unconditionally on $n$, while guarding $\mu = n p^k$ by $k \le n$ and the corrected variance formula (with factor `2`) by $2k - 1 \le n$.

---

## Part III — Unnumbered Prose & Reading Notes (Numbered Statements Are Literal)

### `ISSUE-3.3` (Reading Note on `L748-759` — Function Regularity in Lemma 3.3)
- **Source**: Preamble to Lemma 3.3 (`SteinIntro.tex:748-752`) and Lemma 3.3 (`\label{lem33}`, `SteinIntro.tex:753-759`)
- **Printed text (verbatim)**:
  - Surrounding context (`L750-752`): *"Since our strategy is to apply Theorem \ref{thm31} by estimating the right side of (3.2) for bounded $f$ with bounded first and second derivative, the first lemma shows an expansion of the right side of (3.2) using the structure of $W$ as defined in Theorem \ref{thm32}."*
  - Lemma 3.3 (`L754-758`): *"In the notation of Theorem \ref{thm32}, if $W_i = (\sum_{j \ne i} X_i)/\sqrt{n}$ then $\mathbb{E}[W f(W)] = \mathbb{E}\bigl[\frac{1}{\sqrt{n}}\sum_{i=1}^n X_i(f(W) - f(W_i) - (W - W_i)f'(W))\bigr] + \mathbb{E}\bigl[\frac{1}{\sqrt{n}}\sum_{i=1}^n X_i(W - W_i)f'(W)\bigr]$."*
- **Reading note**: Lemma 3.3 prints no explicit hypothesis on $f$, inheriting from `L750-751` the context of *"bounded $f$ with bounded first and second derivative"*. `SteinMethod.Lem3_3` assumes strictly less (`Differentiable ℝ f`, `f` bounded, and `deriv f` bounded, without requiring second-order differentiability or a bound on $f''$), under which all three expectations in `(3.3)`–`(3.4)` are Bochner-integrable, so `Lem3_3` implies the printed lemma under its surrounding context (`ISSUE-TYPO-3.3` covers the `X_j` summand typo in $W_i$).

---

### `ISSUE-3.5-PROOF-SYM` (Proof Note on `L853-856` — Symmetric Neighborhoods Required for `D^2` Sum Bound in Theorem 3.5)
- **Source**: Proof of Theorem 3.5 (`\label{thm41}`, `SteinIntro.tex:853-856`; `SA-10`, cross-referencing `ISSUE-3.5` in Part II)
- **Printed text (verbatim, `L853-856`)**:
  ```tex
  so that \eqref{447} is bounded above by the first term in the bound \eqref{41}, where we use for example that
  \ba
  \sum_{i=1}^n\sum_{j,k\in N_i}\IE|X_j|^3\leq D^2 \sum_{j=1}^n\IE|X_j|^3.
  \ee
  ```
- **Proof note & counterexample**: Re-indexing $\sum_{i=1}^n \sum_{j, k \in N_i} \mathbb{E}|X_j|^3 = \sum_{j=1}^n (\sum_{i : j \in N_i} |N_i|) \mathbb{E}|X_j|^3$ bounds the coefficient of $\mathbb{E}|X_j|^3$ by $D^2$ only when each $j$ belongs to at most $D$ neighborhoods $N_i$ (which follows from symmetry $j \in N_i \iff i \in N_j$, since $|\{i : j \in N_i\}| = |N_j| \le D$). Under literal Definition 3.1 (`HasDependencyNeighborhoods`, asymmetric $N_i$), take $N_1 = \{1\}$ and $N_i = \{1, i\}$ for $2 \le i \le n$: then $D = \max_i |N_i| = 2$, whereas $\mathbb{E}|X_1|^3$ has coefficient $1 + 2(n - 1) = 2n - 1 \gt 4 = D^2$ for all $n \ge 3$. Together with `(3.15)` in `ISSUE-3.5`, this is the second step in the proof of Theorem 3.5 requiring `IsDependencyGraph` (which includes symmetry `∀ i j, j ∈ N i → i ∈ N j`, already assumed by `SteinMethod.Thm3_5_corrected`).

---

### `ISSUE-3.5-OU` (Reading Note on `L1009-1024` — Small-Time Quadratic Moment Domination in Remark 3.5 Uniqueness)
- **Source**: Remark 3.5 (unlabeled, `SteinIntro.tex:1009-1024`; cross-referencing `ISSUE-TYPO-3.5` in Part I)
- **Printed text (verbatim, `L1018-1019`)**: *"These three properties determine the O-U diffusion process, and this process is reversible with the standard normal distribution as its stationary distribution."*
- **Reading note**:
  - `SteinMethod.Rem3_5` proves literally that the Ornstein–Uhlenbeck transition kernel `ouKernel a` ($x \mapsto \mathcal{N}(e^{-a} x, 1 - e^{-2a})$ for $a \gt 0$) satisfies all three printed infinitesimal properties (`1`–`3`), reversibility with respect to `stdNormalLaw`, stationarity of `stdNormalLaw`, and the $(1 - e^{-a})$-Stein-pair property (`SteinIntro.tex:1021-1023`).
  - Because Remark 3.5 states uniqueness heuristically for *"the O-U diffusion process"* (`L1018-1019`) without specifying a generator domain or uniform-integrability hypothesis for differentiating $\mathbb{E}_x[G(D(t + a))]$ at $a = 0^+$, the project's regularity reading of `"diffusion process"` for the uniqueness direction is formalized in two `_restricted` entries:
    1. `SteinMethod.Rem3_5_uniqueness_probTail_restricted` (`Formalization/Leftovers/OUProbTail.lean`) keeps Ross's literally printed Items `1`–`3` (including the probability tail $(K_a(x))(\{y : |y - x| \gt \varepsilon\}) = o(a)$) for Chapman–Kolmogorov Markov semigroups $(K_t)_{t \gt 0}$ under small-time quadratic moment domination ($\exists a_0, C \gt 0$ such that $\int (y - x)^2\,dK_a(x)(y) \le C a (1 + x^2)$ for $0 \lt a \le a_0$), proving $K_t = \mathrm{ouKernel}\,t$ for all $t \gt 0$ and uniqueness of the stationary distribution `stdNormalLaw`.
    2. `SteinMethod.Rem3_5_uniqueness_restricted` (`Formalization/Leftovers/OUUniqueness.lean`) additionally records infinitesimal Stein-generator and stationary-law uniqueness for general Markov kernel families $(K_a)_{a \gt 0}$ (without assuming Chapman–Kolmogorov) when Item `3` is strengthened to the Lindeberg second-moment tail $\int_{|y - x| \gt \varepsilon} (y - x)^2\,dK_a(x)(y) = o(a)$ alongside small-time quadratic moment domination.

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
  - Unnumbered prose (`L1558-1564`): *"Let $(X_{i,n})_{1\leq n, 1\leq i \leq n}$ be a triangular array of random variables [footnote: That is, for each $n$, $(X_{i,n})_{1\leq i \leq n}$ is a collection of independent random variables.] such that $\mathrm{Var}(X_{i,n})=\sigma_{i,n}^2 \lt \infty$. Let $W_n=\sum_{i=1}^n X_{i,n}$, and assume that $\mathrm{Var}(W_n)=1$. A sufficient condition for $W_n$ to satisfy a CLT as $n\rightarrow\infty$ is the Lindeberg condition: for all $\varepsilon \gt 0$, $\sum_{i=1}^n \mathbb{E}[X_{i, n}^2\mathbb{I}[|X_{i,n}| \gt \varepsilon]]\rightarrow 0$, as $n\rightarrow \infty$."*
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

### `ISSUE-5.2-PROOF` (Proof Note on `L2790-2796` — Twice Differentiability Claim for Locally AC $h$ in Lemma 5.2(2))
- **Source**: Proof of Lemma 5.2(2) (`\label{lem172}` item `\ref{i172}`, `SteinIntro.tex:2790-2796`)
- **Printed text (verbatim, `L2790-2796`)**:
  ```tex
  \item[\ref{i172}.] If $h$ is absolutely continuous, then by the form of \eq{172} it is clear
  that $f_h$ is twice differentiable.  Thus we have that $f_h$ satisfies
  \ba
  f_h''(x)-f_h'(x)=h'(x),
  \ee
  so that we can use the arguments of the proof of the previous item to establish the bounds
  on $\norm{f_h'}$ and $\norm{f_h''}$.
  ```
- **Proof note**: For a general locally absolutely continuous function $h$ with bounded derivative, $f_h$ is everywhere continuously differentiable, but $f_h'$ need not be everywhere differentiable: for $h(t) = \max(t, 0)$ (locally AC, $1$-Lipschitz), $\mathbb{E}[h(Z)] = 1$ and $f_h'(x)$ equals $-e^x$ for $x \lt 0$ and $-1$ for $x \ge 0$, which has a corner at $x = 0$ (left derivative $-1$, right derivative $0$). The printed bound $\|f_h''\| \le 2\|h'\|$ holds everywhere in Lipschitz form as `LipschitzWith (Real.toNNReal (2 * L)) (deriv (expSteinSol h))` alongside `Differentiable ℝ (expSteinSol h)` and `|deriv (deriv (expSteinSol h)) x| ≤ 2 * L` (`SteinMethod.Lem5_2_2`).

---

### `ISSUE-5.9-PROOF-MEAN` (Proof Note on `L3022-3024` — Direct Application of Unit-Mean Theorem 5.4 to $2 Y_n / (n \sigma^2)$)
- **Source**: Proof of Theorem 5.9 (`SteinIntro.tex:3022-3024`)
- **Printed text (verbatim, `L3022-3024`)**:
  ```tex
  We will construct a copy of $Y_n$ and $Y_n^e$ having the equilibrium distribution on the same space and then show that
  $\IE\abs{Y_n-Y_n^e}\leq C \log(n)$.  Once this is established, the result is proved 
  by Theorem \ref{thm172} and the fact that $(cY_n)^e\ed cY_n^e$ for any constant $c$.
  ```
- **Proof note**: Theorem 5.4 (`\label{thm172}`, `L2848`) requires $\mathbb{E}[W] = 1$. For $Y_n \stackrel{d}{=} (Z_n \mid Z_n \gt 0)$ in a critical Galton–Watson process ($\mathbb{E}[Z_n] = 1$), $\mathbb{E}[Y_n] = 1 / \mathbb{P}(Z_n \gt 0)$, so $\mathbb{E}[2 Y_n / (n \sigma^2)] = 2 / (n \sigma^2 \mathbb{P}(Z_n \gt 0))$, which converges to $1$ as $n \to \infty$ when $\sigma^2 \gt 0$ (`Sec5_3_kolmogorov_survival_restricted`) but is not equal to $1$ for finite $n$: for $\mathbb{P}(Z_1 = 0) = \mathbb{P}(Z_1 = 2) = 1/2$ ($\mathbb{E}[Z_1] = 1$, $\sigma^2 = 1$, $\mathbb{E}[Z_1^3] = 4$), $p_n = \mathbb{P}(Z_n \gt 0)$ satisfies $p_{n+1} = p_n(1 - p_n/2)$ ($p_1 = 1/2$, $p_2 = 3/8$, $p_3 = 39/128$), giving $p_n \le 2 / (n + 2)$ and $\mathbb{E}[2 Y_n / (n \sigma^2)] = 2 / (n p_n) \ge 1 + 2/n \gt 1$ for every $n \ge 1$ (machine-checked as `Sec5_3_scaled_Yn_mean_gt_one_witness` / `sec5_3_scaled_Yn_mean_gt_one_witness` in `Formalization/Sweep/SweepE1.lean`).
- **Resolution**: Formalize the witness `Sec5_3_scaled_Yn_mean_gt_one_witness`; the library proof `thm5_9_restricted` (`Thm5_9_restricted` in `Formalization/Branching/YaglomRate.lean`) handles the finite-$n$ mean mismatch via the explicit $|1 - \mathbb{E}[W]|$ mean-discrepancy penalty in `wassersteinDist_le_two_mul_integral_equilibrium_add_abs_mean` and `wassersteinDist_scaled_Y_le`.

---

### `ISSUE-5.9-PROOF` (Proof Notes on `L3160-3164` and `L3176` — Conditional Expectation Chain on `{L_{n,j} = 0}` and Non-`$\sigma(X_j)$`-Measurable RHS)
- **Source**: Proof of Theorem 5.9 (`SteinIntro.tex:3158-3164` and `SteinIntro.tex:3170-3177`)
- **Printed text (verbatim, `L3158-3164` and `L3176-3177`)**:
  ```tex
and using that $S_{n, j}$ and $\I[L_{n,j}=0]$ are negatively correlated (in the second inequality) below, we find
\ba
\IE[R_{n,j}']&=\IE[R_{n,j}|L_{n,j}=0]\\
&\leq \IE[S_{n,j}-1|L_{n,j}=0] \\
	&\leq \IE[S_{n,j}]-1 \\
	&\leq \IE[S_n]-1=\sigma^2.
\ee
  ```
  ```tex
where we have used that $\IE[R_{n,j}\I[L_{n,j}>0]|X_j]\leq X_j \I[L_{n,j}>0]$ in the first inequality
and that $\IP(L_{n,j}>0|X_j=k)\leq k\IP(Z_{n-j}>0)$ in the penultimate inequality.
  ```
- **Proof notes & counterexamples**:
  1. *False intermediate inequality at `L3161` and misstated $\mathbb{E}[S_n] - 1$ at `L3163` (`I-8`)*: Because $S_{n,j} = L_{n,j} + R_{n,j}$ (`L3117-3121`), on the event $\{L_{n,j} = 0\}$ we have $R_{n,j} = S_{n,j}$ identically, so $\mathbb{E}[R_{n,j} \mid L_{n,j} = 0] = \mathbb{E}[S_{n,j} \mid L_{n,j} = 0] = \mathbb{E}[S_{n,j} - 1 \mid L_{n,j} = 0] + 1 \gt \mathbb{E}[S_{n,j} - 1 \mid L_{n,j} = 0]$ (`L3161` is false as written). Moreover, since $S_n = 1 + \sum_{j=1}^n S_{n,j}$ and $\mathbb{E}[S_{n,j}] = \sigma^2$, $\mathbb{E}[S_n] - 1 = n \sigma^2$ rather than $\sigma^2$ (`L3163`). Using negative correlation of $S_{n,j}$ and $\mathbf{1}_{L_{n,j} = 0}$ (`L3158`), the corrected chain $\mathbb{E}[R_{n,j}'] = \mathbb{E}[R_{n,j} \mid L_{n,j} = 0] = \mathbb{E}[S_{n,j} \mid L_{n,j} = 0] \le \mathbb{E}[S_{n,j}] = \sigma^2$ and $\mathbb{E}[S_n] - 1 = n \sigma^2$ is proved as `Sec5_3_neg_corr_3158_and_3160_corrected`.
  2. *Non-$\sigma(X_j)$-measurable right-hand side at `L3176` (`I-9`)*: The right-hand side $X_j \mathbf{1}_{L_{n,j} \gt 0}$ of $\mathbb{E}[R_{n,j}\mathbf{1}_{L_{n,j} \gt 0} \mid X_j] \le X_j \mathbf{1}_{L_{n,j} \gt 0}$ is not $\sigma(X_j)$-measurable, so the inequality is false almost surely: for $Z_1 \in \{0, 3\}$ with probabilities $(2/3, 1/3)$ and $n - j = 1$, $X_j = Z_1^s - 1 \equiv 2$ is deterministic so $\mathbb{E}[R_{n,j}\mathbf{1}_{L_{n,j} \gt 0} \mid X_j] = 1/9 \gt 0$ a.s., whereas on $\{L_{n,j} = 0\}$ (which has probability $19/27 \gt 0$) the right-hand side equals $0 \lt 1/9$. Only the integrated inequality $\mathbb{E}[R_{n,j}\mathbf{1}_{L_{n,j} \gt 0}] \le \mathbb{E}[X_j \mathbf{1}_{L_{n,j} \gt 0}]$ (`L3170`) holds, and it suffices for `Sec5_3_step_ii`.

---

### `ISSUE-6.1` (Reading Note on `L3237` and `L3284` — Integer-Valued Support of $W$ in Section 6)
- **Source**: Lemma 6.1(2) (`\label{lem173}`, `SteinIntro.tex:3237-3238`) and Definition 6.1 (`SteinIntro.tex:3283-3289`)
- **Printed text (verbatim)**:
  - Lemma 6.1(2) (`L3237-3238`): `\item If for some non-negative random variable $W$, $\IE\%{A}f(W)=0$ for all bounded $f$, then $W\sim\Geo(p)$.`
  - Definition 6.1 (`L3284`): `Let $W\geq0$  a random variable with $\IE[W]=(1-p)/p$ for some $0<p\leq 1$.`
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
---

### `ISSUE-THM-4.14` (Proof Note on `L2268` — Triangle-Inequality Step Prints `=` Instead of `≤` in Theorem 4.14)
- **Source**: Proof of Theorem 4.14 (`\label{thm122}`, `SteinIntro.tex:2267-2269`)
- **Printed text (verbatim, `L2267-2269`)**:
  ```tex
  \dtv(W,Z)&\leq \min\{1, \lambda^{-1}\}\sum_{i=1}^n p_i\IE\abs{W+1-W_i}\notag \\
  	&=\min\{1, \lambda^{-1}\}\sum_{i=1}^n p_i\IE\left[\sum_{j\not=i}\left( X_j^{(i)}-X_j\right)+X_i\right] \notag  \\
  	&=\min\{1, \lambda^{-1}\}\sum_{i=1}^n p_i\IE\left[W_i-W-1+2 X_i\right], \label{122}
  ```
- **Proof note**: Since $W = X_i + \sum_{j \ne i} X_j$ and $W_i = 1 + \sum_{j \ne i} X_j^{(i)}$, we have $W + 1 - W_i = X_i - \sum_{j \ne i}(X_j^{(i)} - X_j)$. Because $X_i \ge 0$ and $X_j^{(i)} - X_j \ge 0$ almost surely, the triangle inequality gives $|W + 1 - W_i| \le \sum_{j \ne i}(X_j^{(i)} - X_j) + X_i = W_i - W - 1 + 2 X_i$ (with strict inequality whenever $X_i = 1$ and $\sum_{j \ne i}(X_j^{(i)} - X_j) \ge 1$ co-occur with positive probability). Replacing `=` on `L2268` with `≤` combines with `≤` on `L2267` to yield the exact printed bound of Theorem 4.14 (`SteinMethod.Thm4_14`).

---

### `ISSUE-SEC4.3.2-EXCH` (Proof Note on `L2298-2299` — Subgraph Copy Indicators Are Vertex-Transitive, Not Exchangeable, for $n \ge 5$)
- **Source**: Proof of Theorem 4.15 (`\label{thm123}`, `SteinIntro.tex:2298-2299`)
- **Printed text (verbatim, `L2298-2299`)**:
  ```tex
  Since $W=\sum_{\alpha\in\Gamma}X_\alpha$ is a sum of exchangeable indicators, we can apply Corollary \ref{cor122}
  to construct a size-bias coupling of $W$.
  ```
- **Proof note & machine-checked counterexample (`not_isExchangeableTuple_subgraphCopyIndicator_triangles`)**: While $(X_\alpha)_{\alpha \in \Gamma}$ is **vertex-transitive** (any two copies $\alpha_1, \alpha_2 \in \Gamma$ are related by a vertex permutation of $\mathrm{Fin}\,n$ preserving $G(n, p)$ and the conditional law of $(X_\beta)_{\beta \ne \alpha}$ given $X_\alpha = 1$), the tuple $(X_\alpha)_{\alpha \in \Gamma}$ is **not** exchangeable under all permutations of $\Gamma$ (`IsExchangeableTuple`) for $n \ge 5$. For triangles ($H = K_3$) in $G(5, 1/2)$, $\alpha_0 = \{0, 1, 2\}$ and $\alpha_1 = \{0, 1, 3\}$ share $1$ edge so $\mathbb{E}[X_{\alpha_0} X_{\alpha_1}] = (1/2)^5 = 1/32$, whereas $\alpha_0$ and $\alpha_2 = \{0, 3, 4\}$ share $0$ edges so $\mathbb{E}[X_{\alpha_0} X_{\alpha_2}] = (1/2)^6 = 1/64 \ne 1/32$ (`SteinMethod.not_isExchangeableTuple_subgraphCopyIndicator_triangles` in `Formalization/PoissonSizeBias/Subgraph/IncreasingCoupling.lean`). Theorem 4.15 (`SteinMethod.Thm4_15`) holds literally as printed via Theorem 4.14 with a uniform random copy $I \in \Gamma$ and vertex-permutation symmetry.

---

### `ISSUE-7.2-INT` (Proof Note on `L3541-3544` — Integrability of $(W' - W)(f(W') - f(W))$ Requires Monotonicity or Cross-Integrability)
- **Source**: Proof of Theorem 7.2 (`\label{thm211a}`, `SteinIntro.tex:3541-3544`)
- **Printed text (verbatim, `L3540-3544`)**:
```tex
Let $m(\theta)=\IE[e^{\theta W}]$ and note that $m'(\theta)=\IE[We^{\theta W}]$.  Since $(W,W')$ is
an $a$-Stein pair, we can use \eq{52} to find that for all $f$ such that $\IE\abs{Wf(W)}<\infty$,
\ba
\IE[(W'-W)(f(W')-f(W))]=2a \IE[Wf(W)].
\ee
```
- **Counterexample for general measurable $f$**: $\mathbb{E}|W f(W)| \lt \infty$ alone does not ensure that $(W' - W)(f(W') - f(W))$ is Lebesgue integrable: for i.i.d. $W, W' \sim \mathrm{Unif}[-1, 1]$ (a $1$-Stein pair with $\mathrm{Var}(W) = 1/3 \lt \infty$) and $f(w) = -w^{-1}\mathbf{1}_{w \ne 0}$, $|W f(W)| = 1$ a.s. so $\mathbb{E}|W f(W)| = 1 \lt \infty$, whereas $(W' - W)(f(W') - f(W)) = (W' - W)^2/(W W')$ a.s. has $\mathbb{E}[X^+] = \mathbb{E}[X^-] = +\infty$.
- **Monotone-$f$ rescue (using $\mathbb{E}|W| \lt \infty$ from $\mathrm{Var}(W) \lt \infty$)**: In Theorem 7.2, $\mathrm{Var}(W) \lt \infty$ (`MemLp W 2 P`) implies $\mathbb{E}|W| \lt \infty$ (hence $\mathbb{E}|W'| = \mathbb{E}|W| \lt \infty$ by exchangeability, and $\mathbb{E}[W] = 0$ from Stein-pair linearity). For any monotone (say nondecreasing; negate if nonincreasing) $f$ with $\mathbb{E}|W f(W)| \lt \infty$, define the centered bounded nondecreasing truncations $g_M(w) := \max(-M, \min(f(w) - f(0), M))$ ($M \in \mathbb{N}$):
  1. Since $|g_M| \le M$ and $\mathbb{E}|W| = \mathbb{E}|W'| \lt \infty$, both $|(W' - W)(g_M(W') - g_M(W))| \le 2M(|W'| + |W|)$ and $|W g_M(W)| \le M|W|$ are integrable, so `(3.16)` (`\eq{52}`) gives $\mathbb{E}[(W' - W)(g_M(W') - g_M(W))] = 2a\,\mathbb{E}[W g_M(W)]$.
  2. As $M \to \infty$, clamping is $1$-Lipschitz and order-preserving with $0 \le (w' - w)(g_M(w') - g_M(w)) \uparrow (w' - w)(f(w') - f(w))$ pointwise, so the Monotone Convergence Theorem applies on the LHS; meanwhile $|W g_M(W)| \le |W(f(W) - f(0))| \le |W f(W)| + |f(0)|\,|W| \in L^1$, so the Dominated Convergence Theorem gives $\mathbb{E}[W g_M(W)] \to \mathbb{E}[W(f(W) - f(0))] = \mathbb{E}[W f(W)]$ on the RHS (since $\mathbb{E}[W] = 0$).
  In Theorem 7.2 (`L3547`), $f(w) = e^{\theta w}$ is monotone and $\mathbb{E}[e^{\theta W}|W' - W|] \lt \infty$ is also explicitly assumed (`L3480`), so `(7.3)` holds (`SteinMethod.exchangeable_antisymm_tail_bound`, `SteinMethod.steinPair_tail_bounds`).

---

### `ISSUE-7.6-PROOF` (Proof Note on `L3862` and `L3867-3868` — Unjustified Test Point Under Restricted Domain and Suboptimal Test Point Called Minimizer in Proof of Theorem 7.6(2))
- **Source**: Proof of Theorem 7.6(2) (`\label{thm211c}`, `SteinIntro.tex:3861-3870`)
- **Printed text (verbatim, `L3861-3870`)**:
```tex
Again defining $\tilde m(\theta) = \log(m(\theta))-\mu\theta$, we have $\tilde m'(\theta) \leq C\mu\theta/(1-\frac{C\theta}{2})$ so that
\[\tilde m\left(\frac{\theta}{\sigma}\right) \leq  \frac{ C\mu\theta^2}{\sigma^2\left(2-\frac{C\theta}{\sigma}\right)} \quad\textrm{for } \ 0\leq \theta < \min\{2/C,2\sigma/C\}.\]
We can now apply Proposition \ref{prop211} to find that 
\ban
\IP\left(\frac{X-\mu}{\sigma} \geq t\right) \leq \exp\left(\frac{\mu C \theta^2}{\sigma^2\left(2-\frac{C\theta}{\sigma}\right)} - \theta t\right). \label{2134b}
\ee
The right hand side of this \eq{2134b} is minimized at
\[\theta = t\left(\frac{C\mu}{\sigma^2}+\frac{Ct}{2\sigma}\right)^{-1},\]
and substituting this value into \eq{2134b} yields
the second item of the theorem.
```
- **Proof notes & Counterexamples (`SteinMethod.sec7_3_eq7_12_minimizer_corrected`, `SteinMethod.not_sec7_3_eq7_12_minimizer_printed` / `SteinMethod.not_Sec7_3_eq7_12_minimizer_printed` in `Formalization/Sweep/SweepF.lean`)**:
  1. *Suboptimal test point called minimizer (`L3867-3868`)*: For **every** $C, \mu, \sigma, t \gt 0$, the exponent $g(\theta) = \frac{\mu C \theta^2}{\sigma^2(2 - C\theta/\sigma)} - \theta t$ of `(7.12)` has $g'(\theta_{\mathrm{sub}}) = \frac{\sigma t^2}{4\mu} \gt 0$, while its unique minimizer on $[0, 2\sigma/C)$ is $\theta_{\min} = \frac{2\sigma}{C}\bigl(1 - \sqrt{\mu/(\mu + \sigma t)}\bigr) \lt \theta_{\mathrm{sub}}$ (e.g. at $C = \mu = \sigma = 1, t = 3$, $\theta_{\mathrm{sub}} = 6/5$ gives $e^{-9/5} \gt e^{-2}$ achieved at $\theta_{\min} = 1$).
  2. *Unjustified test-point substitution under `0 \leq \theta < \min\{2/C, 2\sigma/C\}` (`L3862, L3868-3869`)*: Although `L3862`'s inequality holds on $[0, \min\{2/C, 2\sigma/C\})$, restricting `(7.12)` to that interval leaves substituting $\theta_{\mathrm{sub}}$ unjustified whenever $\sigma \gt 1$ and $\theta_{\mathrm{sub}} \ge 2/C$ — e.g. for $X \sim \mathrm{Po}(100), X^s = X + 1$ ($C = 1, \mu = 100, \sigma = 10$) at $t = 100$, $\theta_{\mathrm{sub}} = 50/3 \notin [0, \min\{2/C, 2\sigma/C\}) = [0, 2)$. Rescaling $\tilde m(u) \le \frac{C\mu u^2}{2 - C u}$ from $0 \le u \lt 2/C$ (`L3857`) via $u = \theta/\sigma$ actually yields `(7.12)` on all of $0 \le \theta \lt 2\sigma/C$, which contains $\theta_{\mathrm{sub}}$ and justifies Theorem 7.6(2) (`SteinMethod.sizeBias_tail_bounds`).

---

### `ISSUE-7.2` (Proof / Reading Note on `L3561`, `L3581`, and `L3584` — Strict Signs on $m'(\theta)$ Fail When $W = 0$ a.s.)
- **Source**: Proof of Theorem 7.2 (`\label{thm211a}`, `SteinIntro.tex:3561, 3581-3584`)
- **Printed text (verbatim, `L3561` and `L3581-3584`)**:
```tex
Now, since $m$ is convex and $m'(0)=0$, we find that $m'(\theta)/\theta >0$ for $\theta \not=0$.  We now break the proof into 
```
```tex
\item[$\theta<0$.]  In this case, since $m'(\theta)<0$, \eq{1222h} is bounded above by
$-C \theta m(\theta)$ which implies
\ba
C \theta \leq \frac{d}{d\theta} \log(m(\theta)) < 0.
```
- **Proof note**: When $W = 0$ almost surely (which is permitted in Theorem 7.2, e.g., when $W' = W = 0$ a.s.), $m(\theta) = \mathbb{E}[e^{\theta W}] \equiv 1$ and $m'(\theta) \equiv 0$, so the strict inequalities $m'(\theta)/\theta \gt 0$ and $m'(\theta) \lt 0$ do not hold. However, convexity of $m$ and $m'(0) = 0$ always yield the non-strict inequalities $m'(\theta) \ge 0$ ($\theta \gt 0$) and $m'(\theta) \le 0$ ($\theta \lt 0$), which are all the proof uses (`mgf_tail_bounds_of_abs_deriv_le` in `Formalization/Concentration/Basic.lean`); Theorem 7.2 itself (`Thm7_2`) holds literally as printed.
