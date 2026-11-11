# Core Definitions & Settled Rulings (`SteinMethod`)

This document specifies the core mathematical objects of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex`, SHA-256 `02041ab1408158cebf82f2ec67fed7722ed7594b78728ca00d644a92d67d8d95`), their verified Mathlib names at the pinned commit (`v4.34.0`, `5ed2965256430c3649e86755f9576b54eca72435`), and their settled Lean definitions under [`docs/AUTHOR_RULINGS.md`](AUTHOR_RULINGS.md) (`RULING-USER-2026-11-11`, decisions `D1`–`D9`), implemented in `Formalization/Defs/{AntiVoter,Laws,Metrics,NormalStein,PoissonStein,Couplings,Dependency}.lean` and re-exported by [`Formalization/Defs.lean`](../Formalization/Defs.lean).

---

## 1. Probability Laws (`Formalization/Defs/Laws.lean`)

### 1.1 Normal Law $\mathcal{N}(\mu, \sigma^2)$ and Standard Normal $\mathcal{N}(0, 1)$
- **Source lines**:
  - Standard normal CDF $\Phi(x)$: `SteinIntro.tex:353` (Theorem 1.1 `\label{thm1}`), `SteinIntro.tex:578-588` (Lemma 2.2 `\label{lem2}`)
  - Standard normal distribution and density $\frac{1}{\sqrt{2\pi}} e^{-t^2/2}$: `SteinIntro.tex:562-574` (Lemma 2.1 `\label{lem1}`), `SteinIntro.tex:630-635` (proof of Lemma 2.1)
- **Verified Mathlib objects (`v4.34.0`)**:
  - `ProbabilityTheory.gaussianReal (μ : ℝ) (v : ℝ≥0) : MeasureTheory.Measure ℝ` (`Mathlib.Probability.Distributions.Gaussian.Real`; `v` is the variance $\sigma^2 \in \mathbb{R}_{\ge 0}$, with `gaussianReal μ 0 = Measure.dirac μ` via `gaussianReal_zero_var`)
  - `ProbabilityTheory.gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ` (`(√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))`)
  - `ProbabilityTheory.cdf (μ : MeasureTheory.Measure ℝ) : StieltjesFunction ℝ` (`Mathlib.Probability.CDF`; note `cdf μ x = μ.real (Set.Iic x)` holds under `[IsProbabilityMeasure μ]` via `ProbabilityTheory.cdf_eq_real`, which applies automatically to `stdNormalLaw`)
  - `ProbabilityTheory.HasLaw` (`Mathlib.Probability.HasLaw`)
- **Lean definitions (`Formalization/Defs/Laws.lean`)**:
  ```lean
  noncomputable abbrev normalLaw (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
    ProbabilityTheory.gaussianReal μ v

  noncomputable abbrev stdNormalLaw : Measure ℝ :=
    ProbabilityTheory.gaussianReal 0 1

  noncomputable abbrev stdNormalPDF (x : ℝ) : ℝ :=
    ProbabilityTheory.gaussianPDFReal 0 1 x

  noncomputable abbrev stdNormalCDF (x : ℝ) : ℝ :=
    ProbabilityTheory.cdf stdNormalLaw x
  ```

### 1.2 Poisson Law $\mathrm{Po}(\lambda)$
- **Source lines**:
  - Poisson distribution with mean $\lambda > 0$ and $\mathcal{P}_\lambda(A) = \sum_{k \in A} \frac{\lambda^k e^{-\lambda}}{k!}$ (`\def\P{\%P_\lambda}` at `SteinIntro.tex:310`): `SteinIntro.tex:1823-1848` (Lemmas 4.1–4.2 `\label{lem101}`, `\label{lem102}`)
- **Verified Mathlib objects (`v4.34.0`)**:
  - `ProbabilityTheory.poissonMeasure (r : ℝ≥0) : MeasureTheory.Measure ℕ` (`Mathlib.Probability.Distributions.Poisson.Basic`, scoped notations `Po(r)` and `Po(R, r)`)
  - `ProbabilityTheory.poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) : (poissonMeasure r).real {n} = exp (-r) * r ^ n / n!` (preferred in Mathlib `v4.34.0` over `ProbabilityTheory.poissonPMFReal`, which carries `@[deprecated poissonMeasure (since := "2026-03-08")]`; no custom PMF wrapper is defined)
- **Boundary note at $r = 0$**: Mathlib's `poissonMeasure 0 = Measure.dirac 0`; Section 4 results carry `(hr : 0 < r)` matching `SteinIntro.tex:1824` (`"For \lambda > 0"`).
- **Lean definition (`Formalization/Defs/Laws.lean`)**:
  ```lean
  noncomputable abbrev poissonLaw (r : ℝ≥0) : Measure ℕ :=
    ProbabilityTheory.poissonMeasure r
  ```

---

## 2. Probability Metrics (`Formalization/Defs/Metrics.lean`, Rulings `D1`–`D3`)

- **Source lines**:
  - Integral Probability Metric (IPM), eq. `(1.1)` `\label{23}` (`SteinIntro.tex:503-509`) and eq. `(2.4)` `\label{32}` (`SteinIntro.tex:655-659`)
  - Kolmogorov metric $d_{\mathrm{K}}$ (`SteinIntro.tex:513-515`): $\mathcal{H} = \{\mathbb{I}[\cdot \le x] : x \in \mathbb{R}\}$
  - Wasserstein metric $d_{\mathrm{W}}$ (`SteinIntro.tex:516-519`): $\mathcal{H} = \{h : \mathbb{R} \to \mathbb{R} : |h(x) - h(y)| \le |x - y|\}$
  - Total variation metric $d_{\mathrm{TV}}$ (`SteinIntro.tex:520-521`, Proposition 1.2(3) `SteinIntro.tex:532-535`): $\mathcal{H} = \{\mathbb{I}[\cdot \in A] : A \text{ measurable}\}$ (typo `\I[A\in\IR]` at `L520` recorded in [`docs/SOURCE-ISSUES.md`](SOURCE-ISSUES.md) `ISSUE-TYPO-1.1`)
- **Verified Mathlib objects (`v4.34.0`)**:
  - `LipschitzWith (1 : ℝ≥0) h` (`Mathlib.Topology.MetricSpace.Lipschitz`, `lipschitzWith_iff_dist_le_mul`)
  - `Set.Iic x`, `Set.indicator A (1 : α → ℝ)`
  - `MeasureTheory.Integrable`, `MeasureTheory.integral`, `MeasureTheory.Measure.real`
  - `MeasureTheory.SignedMeasure.totalVariation` (`Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan`)
- **Settled choices (`D1`–`D3`)**:
  - **`D1` (`ℝ≥0∞` codomain with `Integrable` guard)**: Every metric takes values in `ℝ≥0∞` via `⨆` over integrable test functions in `H`. Because `ℝ≥0∞` is a complete lattice, `wassersteinDist` evaluates to `⊤` on heavy-tailed laws lacking a finite first moment rather than collapsing to `0`, so statements quantifying over *"any random variable $W$"* (such as Proposition 1.2(2) and Theorem 3.1) require **no** unprinted moment hypotheses.
  - **`D2` (Measure signatures)**: Metrics take `(μ ν : Measure α)`. Statements about random variables pass `P.map W` with `[IsProbabilityMeasure P]` and `AEMeasurable W P` (or `HasLaw`).
  - **`D3` (Polymorphic TV carrier)**: `tvDist` is polymorphic over `{α : Type*} [MeasurableSpace α]`; the countable discrete formula $\frac{1}{2}\sum_\omega |\mathbb{P}(W = \omega) - \mathbb{P}(Z = \omega)|$ is proved as Proposition 1.2(3).
- **Lean definitions (`Formalization/Defs/Metrics.lean`)**:
  ```lean
  noncomputable def ipm {α : Type*} [MeasurableSpace α]
      (H : Set (α → ℝ)) (μ ν : Measure α) : ℝ≥0∞ :=
    ⨆ h ∈ H, ⨆ (_ : Integrable h μ ∧ Integrable h ν),
      ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)|

  noncomputable def kolmogorovDist (μ ν : Measure ℝ) : ℝ≥0∞ :=
    ipm {h : ℝ → ℝ | ∃ x : ℝ, h = (Set.Iic x).indicator 1} μ ν

  noncomputable def wassersteinDist (μ ν : Measure ℝ) : ℝ≥0∞ :=
    ipm {h : ℝ → ℝ | LipschitzWith 1 h} μ ν

  noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
    ipm {h : α → ℝ | ∃ A : Set α, MeasurableSet A ∧ h = A.indicator 1} μ ν
  ```

---

## 3. Stein Operators, Solutions, and Classes

### 3.1 Normal Stein Objects (`Formalization/Defs/{NormalStein,Kolmogorov}.lean`, Rulings `D4`–`D6`)
- **Source lines**:
  - Standard normal expectation $\Phi(h) := \mathbb{E}[h(Z)]$: `SteinIntro.tex:663`
  - Normal Stein operator $\mathcal{A}f(w) = f'(w) - w f(w)$: `SteinIntro.tex:563-566` (Lemma 2.1 `\label{lem1}`)
  - Normal Stein solution $f_h(w) = e^{w^2/2}\int_w^\infty e^{-t^2/2}(\Phi(h) - h(t))\,dt$: `SteinIntro.tex:681-683` (Lemma 2.5 `\label{lem31}`) and `SteinIntro.tex:584-587` (Lemma 2.2 `\label{lem2}` for $h = \mathbb{I}[\cdot \le x]$)
  - Wasserstein Stein test class $\mathcal{F} = \{f : \|f\|, \|f''\| \le 2,\ \|f'\| \le \sqrt{2/\pi}\}$: `SteinIntro.tex:719-724` (Theorem 3.1 `\label{thm31}`)
  - Kolmogorov Stein test class $\mathcal{F}$ of functions satisfying the bounds of Lemma 3.25 (`\label{lem91}`, `SteinIntro.tex:1677-1686`): `SteinIntro.tex:1688-1694` (Corollary 3.26 `\label{cor91}`)
- **Verified Mathlib objects (`v4.34.0`)**:
  - `deriv`, `derivWithin`, `HasDerivAt`, `Differentiable` (`Mathlib.Analysis.Calculus.Deriv.Basic`)
  - `AbsolutelyContinuousOnInterval` (`Mathlib.MeasureTheory.Function.AbsolutelyContinuous`), with FTC theorem `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` (`Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`)
- **Settled choices (`D4`–`D6`)**:
  - **`D4`**: `normalSteinOp` uses two-sided `deriv`. `normalSteinOpLeft` (`derivWithin f (Set.Iic w) w - w * f w`) is used **only** in `_corrected` statements backed by [`docs/SOURCE-ISSUES.md`](SOURCE-ISSUES.md) (`ISSUE-2.2`: `Lem2_2_corrected`, `Cor2_3_corrected`, `Thm3_24_corrected`, `Lem3_25_corrected`).
  - **`D5`**: "Absolutely continuous" on $\mathbb{R}$ means locally AC: `∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b`, with `deriv f` and `Integrable (deriv f) stdNormalLaw`.
  - **`D6`**: `normalWassersteinClass` uses the literal twice-differentiable class with uniform bounds `2`, `√(2/π)`, and `2`. Parallel to `D6`, `normalKolmogorovClass` (`Formalization/Defs/Kolmogorov.lean`) uses the literal differentiable class satisfying Lemma 3.25's bounds (`√(π/2)`, `2`, and `|(w + u) * f (w + u) - (w + v) * f (w + v)| ≤ (|w| + √(2π)/4) * (|u| + |v|)`), with non-vacuity witness `exists_ne_zero_mem_normalKolmogorovClass` in `Formalization/Kolmogorov/Basic.lean`.
- **Lean definitions (`Formalization/Defs/NormalStein.lean`, `Formalization/Defs/Kolmogorov.lean`)**:
  ```lean
  noncomputable def stdNormalExpect (h : ℝ → ℝ) : ℝ :=
    ∫ x, h x ∂(ProbabilityTheory.gaussianReal 0 1)

  noncomputable def normalSteinOp (f : ℝ → ℝ) (w : ℝ) : ℝ :=
    deriv f w - w * f w

  noncomputable def normalSteinSol (h : ℝ → ℝ) (w : ℝ) : ℝ :=
    Real.exp (w ^ 2 / 2) *
      ∫ t in Set.Ioi w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)

  noncomputable def normalSteinSolKolm (x : ℝ) : ℝ → ℝ :=
    normalSteinSol ((Set.Iic x).indicator 1)

  noncomputable def normalSteinOpLeft (f : ℝ → ℝ) (w : ℝ) : ℝ :=
    derivWithin f (Set.Iic w) w - w * f w

  def normalWassersteinClass : Set (ℝ → ℝ) :=
    {f | Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧
      (∀ w, |f w| ≤ 2) ∧ (∀ w, |deriv f w| ≤ Real.sqrt (2 / Real.pi)) ∧
      (∀ w, |deriv (deriv f) w| ≤ 2)}

  def normalKolmogorovClass : Set (ℝ → ℝ) :=
    {f | Differentiable ℝ f ∧
      (∀ w : ℝ, |f w| ≤ Real.sqrt (Real.pi / 2)) ∧
      (∀ w : ℝ, |deriv f w| ≤ 2) ∧
      (∀ u v w : ℝ,
        |(w + u) * f (w + u) - (w + v) * f (w + v)| ≤
          (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|))}
  ```

### 3.2 Poisson Stein Objects (`Formalization/Defs/PoissonStein.lean`, Finding `H6`)
- **Source lines**:
  - Poisson Stein operator $\mathcal{A}f(k) = \lambda f(k + 1) - k f(k)$: `SteinIntro.tex:1824-1827` (Lemma 4.1 `\label{lem101}`)
  - Canonical solution $f_A$ of $\lambda f_A(k+1) - k f_A(k) = \mathbb{I}[k \in A] - \mathcal{P}_\lambda(A)$ with $f_A(0) = 0$: `SteinIntro.tex:1837-1848` (Lemma 4.2 `\label{lem102}`)
  - Forward difference $\Delta f(k) := f(k + 1) - f(k)$: `SteinIntro.tex:1885` (Lemma 4.4 `\label{lem103}`)
- **Verified Mathlib objects (`v4.34.0`)**:
  - `_root_.fwdDiff 1 f k = f (k + 1) - f k` (`Mathlib.Algebra.Group.ForwardDiff`; reused directly without redefining `SteinMethod.fwdDiff`)
  - `Nat.factorial`, `Set.Iio`
- **Lean definitions (`Formalization/Defs/PoissonStein.lean`)**:
  ```lean
  def poissonSteinOp (r : ℝ≥0) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
    (r : ℝ) * f (k + 1) - (k : ℝ) * f k

  noncomputable def poissonSteinSol (r : ℝ≥0) (A : Set ℕ) : ℕ → ℝ
    | 0 => 0
    | k + 1 =>
        ((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
          ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
            (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1)))
  ```

---

## 4. Couplings (`Formalization/Defs/Couplings.lean`, Rulings `D7`–`D9`)

### 4.1 Exchangeable Pair and $a$-Stein Pair (`D7`)
- **Source lines**: Definition 3.2 (`SteinIntro.tex:952-960`): *"The ordered pair $(W, W')$ of random variables is called an exchangeable pair if $(W, W') \stackrel{d}{=} (W', W)$. If for some $0 < a \le 1$, the exchangeable pair $(W, W')$ satisfies the relation $\mathbb{E}[W' \mid W] = (1 - a)W$, then we call $(W, W')$ an $a$-Stein pair."*
- **Verified Mathlib objects (`v4.34.0`)**:
  - `ProbabilityTheory.IdentDistrib` (`Mathlib.Probability.IdentDistrib`)
  - `MeasureTheory.condExp (MeasurableSpace.comap W inferInstance) P W'` (`Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`)
- **Settled choice (`D7`)**: `IsSteinPair` uses `0 < a ∧ a ≤ 1` as printed, together with `Measurable W` and `Integrable W P` so the sub-$\sigma$-algebra `comap W` is sub-measurable and `condExp` is non-junk. Library theorems are proved for any `0 < a` (covering Example 7.5 at $n = 2$, recorded in `ISSUE-7.5`).

### 4.2 Size-Bias Distribution (`D8`)
- **Source lines**: Definition 3.7 (`SteinIntro.tex:1224-1230`): *"For a random variable $X \ge 0$ with $\mathbb{E}[X] = \mu < \infty$, we say the random variable $X^s$ has the size-bias distribution with respect to $X$ if for all $f$ such that $\mathbb{E}|X f(X)| < \infty$ we have $\mathbb{E}[X f(X)] = \mu \mathbb{E}[f(X^s)]$."*
- **Settled choice (`D8`)**: Literal definition allowing $\mu = 0$, with typing `0 ≤ᵐ[P] X`, `Integrable X P`, `AEMeasurable Xs P'`, and quantifying over measurable `f` with `Integrable (fun ω ↦ X ω * f (X ω)) P` (no extra conclusion-side integrability). Proposition 3.11 is restricted to `0 < μ` (`ISSUE-3.11`).

### 4.3 Zero-Bias Distribution (`D9`)
- **Source lines**: Definition 3.10 (`SteinIntro.tex:1442-1449`): *"For a random variable $W$ with $\mathbb{E}[W] = 0$ and $\mathrm{Var}(W) = \sigma^2 < \infty$, we say the random variable $W^z$ has the zero-bias distribution with respect to $W$ if for all absolutely continuous $f$ such that $\mathbb{E}|W f(W)| < \infty$ we have $\mathbb{E}[W f(W)] = \sigma^2 \mathbb{E}[f'(W^z)]$."*
- **Verified Mathlib objects (`v4.34.0`)**:
  - `MeasureTheory.MemLp W 2 P` (`Mathlib.MeasureTheory.Function.LpSpace.Basic`)
  - `ProbabilityTheory.variance W P` (`Mathlib.Probability.Moments.Variance`; note `variance W P = (evariance W P).toReal`, which is `0` off $L^2$, hence `MemLp W 2 P` is required)
- **Settled choice (`D9` + confirmed `H4`)**: As proved in [`docs/SOURCE-ISSUES.md`](SOURCE-ISSUES.md) (`ISSUE-3.10`), when $\mathbb{E}|W|^3 = \infty$ there exist $C^1$ functions $f$ with $\mathbb{E}|W f(W)| < \infty$ for which $\int |f'|\,p^z = \infty$, so no probability distribution satisfies the literal quantifier. Per `D9`, `IsZeroBias` quantifies over locally AC `f` (`∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b`) for which **both** `Integrable (fun ω ↦ W ω * f (W ω)) P` and `Integrable (fun ω' ↦ deriv f (Wz ω')) P'` hold.

- **Lean definitions (`Formalization/Defs/Couplings.lean`)**:
  ```lean
  def IsExchangeablePair {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
      (P : Measure Ω) (W W' : Ω → α) : Prop :=
    ProbabilityTheory.IdentDistrib (fun ω ↦ (W ω, W' ω)) (fun ω ↦ (W' ω, W ω)) P P

  def IsSteinPair {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) (a : ℝ) (W W' : Ω → ℝ) : Prop :=
    IsExchangeablePair P W W' ∧ 0 < a ∧ a ≤ 1 ∧ Measurable W ∧ Integrable W P ∧
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω

  def IsSizeBias {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) (X : Ω → ℝ) (P' : Measure Ω') (Xs : Ω' → ℝ) : Prop :=
    (0 ≤ᵐ[P] X) ∧ Integrable X P ∧ AEMeasurable Xs P' ∧
      ∀ f : ℝ → ℝ, Measurable f → Integrable (fun ω ↦ X ω * f (X ω)) P →
        ∫ ω, X ω * f (X ω) ∂P = (∫ ω, X ω ∂P) * ∫ ω', f (Xs ω') ∂P'

  def IsZeroBias {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) (W : Ω → ℝ) (P' : Measure Ω') (Wz : Ω' → ℝ) : Prop :=
    MemLp W 2 P ∧ ∫ ω, W ω ∂P = 0 ∧ AEMeasurable Wz P' ∧
      ∀ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
        Integrable (fun ω ↦ W ω * f (W ω)) P →
        Integrable (fun ω' ↦ deriv f (Wz ω')) P' →
        ∫ ω, W ω * f (W ω) ∂P =
          ProbabilityTheory.variance W P * ∫ ω', deriv f (Wz ω') ∂P'
  ```
- **Canonical zero-bias density (`Formalization/Defs/ZeroBias.lean`)**:
  - **Source lines**: Proposition 3.19(2) (`\label{i82}`, eq. `(3.32)` `\label{82}`, `SteinIntro.tex:1479-1484`): $p^z(w) = \sigma^{-2}\,\mathbb{E}[W \mathbb{I}[W > w]]$.
  - **Non-vacuity witnesses (`Formalization/ZeroBias/Basic.lean`)**: `isZeroBias_stdNormal : IsZeroBias stdNormalLaw id stdNormalLaw id` and `zeroBiasDensity_stdNormal : ∀ w : ℝ, zeroBiasDensity stdNormalLaw id w = stdNormalPDF w`.
  ```lean
  noncomputable def zeroBiasDensity {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) (W : Ω → ℝ) (w : ℝ) : ℝ :=
    (ProbabilityTheory.variance W P)⁻¹ * ∫ ω, W ω * (Set.Ioi w).indicator 1 (W ω) ∂P
  ```

### 4.4 Dependency Neighborhoods and Dependency Graphs (`Formalization/Defs/Dependency.lean`)
- **Source lines**:
  - Definition 3.1 (`SteinIntro.tex:805-809`): *"We say that a collection of random variables $(X_1, \ldots, X_n)$ has dependency neighborhoods $N_i \subseteq \{1, \ldots, n\}$, $i = 1, \ldots, n$, if $X_i$ is independent of $\{X_j\}_{j \notin N_i}$."*
  - Dependency graph prose (`SteinIntro.tex:810-812`): *"If we think of constructing a graph with vertices $\{1, \ldots, n\}$ where if there is no edge between $i$ and $j$ then $X_i$ and $X_j$ are independent, then we can define $N_i / \{i\}$ as the neighbors of vertex $i$ in the graph. For this reason, dependency neighborhoods are frequently referred to as dependency graphs."*
- **Verified Mathlib objects (`v4.34.0`)**:
  - `ProbabilityTheory.IndepFun` (`Mathlib.Probability.Independence.Basic`)
  - `Finset (Fin n)`
- **Lean definitions (`Formalization/Defs/Dependency.lean`)**:
  ```lean
  def HasDependencyNeighborhoods {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
      (X : Fin n → Ω → ℝ) (N : Fin n → Finset (Fin n)) : Prop :=
    ∀ i, ProbabilityTheory.IndepFun (X i) (fun ω (j : {j // j ∉ N i}) ↦ X j ω) P

  def IsDependencyGraph {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
      (X : Fin n → Ω → ℝ) (N : Fin n → Finset (Fin n)) : Prop :=
    (∀ i, i ∈ N i) ∧ (∀ i j, j ∈ N i → i ∈ N j) ∧
    ∀ A B : Finset (Fin n), (∀ a ∈ A, ∀ b ∈ B, b ∉ N a) →
      ProbabilityTheory.IndepFun (fun ω (a : A) ↦ X a ω) (fun ω (b : B) ↦ X b ω) P
  ```

### 4.5 Anti-Voter Model (`Formalization/Defs/AntiVoter.lean`)
- **Source lines**:
  - Anti-voter Markov chain on $\{-1, 1\}^V$: `SteinIntro.tex:1101-1108`
  - Theorem 3.8 (`\label{thm52}`): `SteinIntro.tex:1114-1127`
  - Cut-defect parameter $\kappa(G)$ and Lemma 3.10: `SteinIntro.tex:1208-1214`
- **Verified Mathlib objects (`v4.34.0`)**:
  - `SimpleGraph`, `SimpleGraph.neighborFinset`, `SimpleGraph.edgeFinset`, `SimpleGraph.IsRegularOfDegree` (`Mathlib.Combinatorics.SimpleGraph.Finite`)
  - `SimpleGraph.IsBipartite` (`Mathlib.Combinatorics.SimpleGraph.Bipartite`), `SimpleGraph.cycleGraph` (`Mathlib.Combinatorics.SimpleGraph.CycleGraph`), `SimpleGraph.Iso` (`≃g`, `Mathlib.Combinatorics.SimpleGraph.Maps`)
  - `Finset.sym2` (`Mathlib.Data.Finset.Sym`)
  - `PMF.uniformOfFinset`, `PMF.bind`, `PMF.map`, `PMF.pure` (`Mathlib.Probability.Distributions.Uniform`, `Mathlib.Probability.ProbabilityMassFunction.Constructions`)
- **Representation and totality conventions**:
  - Vertex labelings are functions `V → Bool` (equipped with the discrete product measurable space), read into $\{-1, 1\} \subset \mathbb{R}$ via `spin b := if b then 1 else -1`, with opposite label `!b`.
  - In `antiVoterStep G x`, if `V` is empty or the uniformly chosen vertex `v` has empty `G.neighborFinset v`, the chain stays at `x` (`PMF.pure x`). This is purely a totality convention: under the hypotheses of `Thm3_8` (`G.IsRegularOfDegree r` and `¬ G.IsBipartite`, which force `3 ≤ Fintype.card V` and `1 ≤ r`) and `Lem3_10` (`G.IsRegularOfDegree r` and `0 < r` on nonempty `V`), every vertex has $r \ge 1$ neighbors so the fallback branch is never taken.
  - `kappa G` takes the minimum over `A : Finset V` via `Finset.univ.inf'` (since `ℕ` has no `⊤` element) of the cardinality of edges in `G.edgeFinset` (each undirected edge counted once) with both endpoints in `A` (`e ∈ A.sym2`) or both endpoints in `Aᶜ` (`e ∈ Aᶜ.sym2`).
- **Lean definitions (`Formalization/Defs/AntiVoter.lean`)**:
  ```lean
  def spin (b : Bool) : ℝ :=
    if b then 1 else -1

  noncomputable def antiVoterStep {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool) : PMF (V → Bool) :=
    if hV : (Finset.univ : Finset V).Nonempty then
      (PMF.uniformOfFinset Finset.univ hV).bind fun v ↦
        if hN : (G.neighborFinset v).Nonempty then
          (PMF.uniformOfFinset (G.neighborFinset v) hN).map fun u ↦ Function.update x v (!x u)
        else
          PMF.pure x
    else
      PMF.pure x

  def IsAntiVoterStationary {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) : Prop :=
    ∀ y : V → Bool, ν {y} = ∑ x : V → Bool, ν {x} * antiVoterStep G x y

  def kappa {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
    Finset.univ.inf' Finset.univ_nonempty fun A : Finset V ↦
      (G.edgeFinset.filter fun e ↦ e ∈ A.sym2 ∨ e ∈ Aᶜ.sym2).card
  ```

### 4.6 Erdős–Rényi Random Graphs (`Formalization/Defs/RandomGraph.lean`)
- **Source lines**:
  - Section 3.2.1 (`SteinIntro.tex:918-920`): *"Let $G = G(n, p)$ be an Erdős–Rényi random graph on $n$ vertices with edge probability $p$..."*
  - Example 3.9 (`\label{ex72}`, `SteinIntro.tex:1354-1358`) and Theorem 3.17 (`SteinIntro.tex:1413-1420`): *"Let $G = G(n, p)$ be an Erdős–Rényi graph..."*
  - Section 4.1.2 / 4.2.1 (`SteinIntro.tex:2071-2078, 2176-2246, 2334-2366`)
- **Verified Mathlib objects (`v4.34.0`)**:
  - `SimpleGraph (Fin n)`, `SimpleGraph.fromEdgeSet`, `SimpleGraph.edgeSet`, `SimpleGraph.IsIsolated`, `SimpleGraph.neighborSet` (`Mathlib.Combinatorics.SimpleGraph.Basic`)
  - `SimpleGraph.deleteIncidenceSet` (`Mathlib.Combinatorics.SimpleGraph.DeleteEdges`), `SimpleGraph.cliqueSet` (`Mathlib.Combinatorics.SimpleGraph.Clique`), `Set.ncard` (`Mathlib.Data.Set.Card`)
  - `MeasurableSpace (SimpleGraph V) := .comap Adj inferInstance`, `SimpleGraph.measurable_iff_adj`, `SimpleGraph.measurable_edgeSet` (`Mathlib.MeasureTheory.Constructions.SimpleGraph`)
  - `MeasureTheory.Measure.pi` (`Mathlib.MeasureTheory.Constructions.Pi`)
  - `ProbabilityTheory.bernoulliMeasure`, `Set.projIcc` (`Mathlib.Probability.Distributions.Bernoulli`, `Mathlib.Topology.UnitInterval`)
- **Representation and totality conventions**:
  - Potential undirected edges on `Fin n` are indexed by `EdgePair n := {e : Sym2 (Fin n) // ¬ e.IsDiag}`, a finite type of cardinality $\binom{n}{2}$.
  - `graphOfEdgeBits : (EdgePair n → Bool) → SimpleGraph (Fin n)` sends each boolean edge-presence vector `ω` to `SimpleGraph.fromEdgeSet {e | ∃ h, ω ⟨e, h⟩ = true}`, establishing a measurable bijection between `EdgePair n → Bool` and `SimpleGraph (Fin n)`.
  - `erdosRenyi n p : Measure (SimpleGraph (Fin n))` pushes forward the product measure `Measure.pi (fun _ : EdgePair n ↦ ProbabilityTheory.bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p))` along `graphOfEdgeBits`. Clamping `p` to $[0, 1]$ via `Set.projIcc` is a totality convention so `erdosRenyi n p` takes `(n : ℕ) (p : ℝ)` without proof arguments; for `0 ≤ p ≤ 1`, `Set.projIcc 0 1 zero_le_one p = ⟨p, hp₀, hp₁⟩`, `erdosRenyi n p` is a probability measure, and the $\binom{n}{2}$ edge indicators `edgeIndicator e` are i.i.d. $\mathrm{Bernoulli}(p)$ (`Formalization/RandomGraph/ErdosRenyi.lean`).
  - Graph observables on measurable variables `G : SimpleGraph (Fin n)` are expressed using decidability-free Mathlib primitives (`G.IsIsolated i`, `(G.neighborSet i).ncard`, `G.deleteIncidenceSet i`, `(G.cliqueSet 3).ncard`) so statements avoid classical `[DecidableRel G.Adj]` instance parameters.
- **Lean definitions (`Formalization/Defs/RandomGraph.lean`)**:
  ```lean
  abbrev EdgePair (n : ℕ) : Type :=
    {e : Sym2 (Fin n) // ¬ e.IsDiag}

  def graphOfEdgeBits {n : ℕ} (ω : EdgePair n → Bool) : SimpleGraph (Fin n) :=
    SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | ∃ h : ¬ e.IsDiag, ω ⟨e, h⟩ = true}

  noncomputable def erdosRenyi (n : ℕ) (p : ℝ) : Measure (SimpleGraph (Fin n)) :=
    (Measure.pi fun _ : EdgePair n ↦
      ProbabilityTheory.bernoulliMeasure true false
        (Set.projIcc 0 1 zero_le_one p)).map graphOfEdgeBits

  noncomputable def edgeIndicator {n : ℕ} (e : EdgePair n) (G : SimpleGraph (Fin n)) : ℝ :=
    {H : SimpleGraph (Fin n) | e.1 ∈ H.edgeSet}.indicator 1 G
  ```

---

## 5. Formalization Notes

1. **Lemma 2.5(2) (`Lem2_5_2`, `\label{lem31}` item `\label{i32}`, `SteinIntro.tex:690-694`; `review-01.md` `L1`)**:
   - Printed text: *"If $h$ is absolutely continuous, then $\|f_h\| \le 2\|h'\|$, $\|f_h'\| \le \sqrt{\frac{2}{\pi}}\|h'\|$, and $\|f_h''\| \le 2\|h'\|$."*
   - When $\|h'\|_\infty = \infty$, the printed extended-real inequalities in $[0, \infty]$ hold vacuously, whereas Lean's real-valued `sSup` on an unbounded subset of `ℝ` returns `0`. Quantifying over every finite uniform derivative bound `∀ L : ℝ, (∀ t, |deriv h t| ≤ L) → (∀ w, |normalSteinSol h w| ≤ 2 * L) ∧ (∀ w, |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi) * L) ∧ (∀ w, |deriv (deriv (normalSteinSol h)) w| ≤ 2 * L)` (for locally AC `h`) is therefore the literal real-valued statement of Lemma 2.5(2), formalized as `Lem2_5_2` without a `_restricted` suffix.

2. **Proposition 2.4 (`Prop2_4`, `\label{prop31}`, `SteinIntro.tex:665-670`) right-hand side integrability guard (`D1` critic spec)**:
   - Under `D1`, `ipm H (P.map W) (P'.map Z)` guards test functions in `H` by `Integrable h (P.map W) ∧ Integrable h (P'.map Z)`.
   - Per the critic's Batch 2 specification (`review-01.md` L137, `NEXT-PROMPT.md` L66–70), the right-hand supremum in display `(2.5)` (`\label{31}`, `SteinIntro.tex:667-669`) carries the identical `D1` integrability guard:
     ```lean
     ipm H (P.map W) (P'.map Z) =
       ⨆ h ∈ H, ⨆ (_ : Integrable h (P.map W) ∧ Integrable h (P'.map Z)),
         ENNReal.ofReal |∫ ω, normalSteinOp (f h) (W ω) ∂P|
     ```
     so both sides of `(2.5)` range over the exact same test functions without Bochner-integral junk zeros.

3. **Theorem 5.7 (`\label{thm1710}`, `SteinIntro.tex:2915-2929`, bounds `(5.4)`–`(5.5)` at `L2924-2928`) Lean encoding note (`review-01.md` `L1`)**:
   - Lean's totalized real division (`0 / 0 = 0`), `sSup` fallback `0` on unbounded sets in `ℝ`, and Bochner integral fallback `0` on non-integrable functions (such as `∫ ω, |(N ω : ℝ) - M ω| ∂P` when $\mathbb{E}[N] = 1/p < \infty$ but $\mathbb{E}|N - M| = \infty$, where the mathematical extended-real upper bound in $[0, \infty]$ is trivially $+\infty$) are Lean encoding conventions rather than mathematical defects in the source, and require either `ℝ≥0∞` `lintegral`/`iSup` or explicit positivity/integrability hypotheses (`0 < p`, `Integrable`; similarly `0 < r` for $\lambda > 0$ in Section 4 where `0 / 0 = 0` would otherwise mask division by $\lambda = 0$). [`docs/SOURCE-ISSUES.md`](SOURCE-ISSUES.md) (`ISSUE-5.7`) records only the genuine mathematical issues in Theorem 5.7 (omitted $m \ge 1$ support in `L2920` and omitted joint independence of $(N, M)$ from $(X_i)_{i \ge 1}$).

4. **Statement & Proof Wrapper Module Layout (`AGENTS.md` Rule 5, `review-01.md` `L2`)**:
   - Every proved survey result is stated as a self-contained `def <Name> : Prop` in `Formalization/Statements/SecN.lean` (which imports `Formalization.Defs` only) and proved as `theorem <Name>_holds : <Name>` in `Formalization/Statements/SecNProofs.lean`.

5. **Non-Empty Finite Index Typing (`0 < n`)**:
   - Where the source writes a finite family $X_1, \ldots, X_n$ ($1$-indexed, tacitly $n \ge 1$) and divides by $n$ or $\sqrt{n}$ (e.g., Theorem 3.2, Lemmas 3.3–3.4, and Example 3.6, where Example 3.6 also draws $I$ uniformly from $\{1, \ldots, n\}$), Lean's `Fin n` allows $n = 0$ (where `Fin 0` is empty and real division by $0$ evaluates to `0`). Statements of this form include `0 < n` as a standard non-empty finite-family typing condition rather than a source correction.

6. **Positive Degree Typing (`0 < r`) in Lemma 3.10 (`Lem3_10`, `SteinIntro.tex:1208-1214`)**:
   - In the anti-voter chain on an $r$-regular graph $G$, each step uniformly chooses a neighbor of the selected vertex $v$, which is undefined when $r = 0$, and Lemma 3.10's lower bound $\frac{2\kappa(G)}{r} \le \sigma^2$ divides by $r$. `Lem3_10` therefore includes `0 < r` as a typing/well-definedness condition (whereas in `Thm3_8`, `1 ≤ r` and `3 ≤ Fintype.card V` follow automatically from `G.IsRegularOfDegree r` and `¬ G.IsBipartite`).

7. **Measurability (`Measurable X`) When Conditioning on `X`**:
   - Mathlib's conditional expectation `P[Y | MeasurableSpace.comap X inferInstance]` returns the junk value `0` unless `MeasurableSpace.comap X inferInstance` is a sub-$\sigma$-algebra of the ambient measurable space on `Ω`, i.e., `Measurable X` (and similarly `condDistrib` and `ProbabilityTheory.cond P (X i ⁻¹' {1})` require measurable conditioning maps). Statements that condition on a random variable `X` (such as `Thm3_13`, `Prop3_14`, `Cor3_15`, and `Cor3_16`, matching `IsSteinPair`) therefore carry `Measurable X` as the typing condition for non-junk conditioning.

8. **Positive Total Mean (`0 < μ`) in Size-Bias Mixture Couplings (`Prop3_14`, `Cor3_15`, `Cor3_16`)**:
   - Where the source chooses a random summand index $I \in \{1, \ldots, n\}$ with $\mathbb{P}(I = i) = \mu_i / \mu$ (`SteinIntro.tex:1292-1293, 1322-1323, 1330-1331`), formalized as `∀ i, P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / μ` (or `p i / μ` in `Cor3_16`), the source divides by $\mu = \sum_i \mu_i$ (and for $\mu = 0$ no index distribution can have weights $\mu_i / \mu$ summing to $1$). `0 < μ` is therefore included as a well-definedness condition.

9. **Isolated-Vertex Size-Bias Realization Well-Definedness (`0 < n`, `p < 1`) in `Ex3_9_sizeBias` (`SteinIntro.tex:1360-1367`)**:
   - Example 3.9 draws a uniform random vertex $I \in \{1, \ldots, n\}$ (`0 < n` non-empty index typing, §5.5) and applies Corollary 3.16 (`\label{cor72}`) to $X = \sum_{i=1}^n X_i$, which requires $\mu = n(1 - p)^{n - 1} > 0$ (§5.8), i.e., $p < 1$ when $n \ge 2$ (and at $p = 1, n \ge 2$, $G(n, 1) = K_n$ has $X \equiv 0$, whereas erasing edges at $v_I$ produces $X^s \ge 1$). `Ex3_9_sizeBias` therefore assumes `0 < n`, `0 ≤ p`, and `p < 1`.

---

## 6. Geometric Approximation (`Formalization/Defs/Geometric.lean`)

1. **`SteinMethod.geomLaw` and `SteinMethod.posGeomLaw`** (`SteinIntro.tex:2884, 3194-3200, 3223-3225`):
   - `geomLaw (p : ℝ) : Measure ℕ := ProbabilityTheory.geometricMeasure (Set.projIcc 0 1 zero_le_one p)` models $\mathrm{Ge}^0(p)$ on $\mathbb{N} = \{0, 1, 2, \dots\}$ with $\mathbb{P}(N = k) = (1 - p)^k p$ for $0 < p \le 1$.
   - `posGeomLaw (p : ℝ) : Measure ℕ := (geomLaw p).map (· + 1)` models $\mathrm{Ge}(p)$ on $\{1, 2, \dots\}$ with $\mathbb{P}(X = k) = (1 - p)^{k - 1} p$ for $k \ge 1$.
2. **`SteinMethod.geomSteinOp`, `SteinMethod.geomSteinSol`, and `SteinMethod.geomSteinClass`** (`SteinIntro.tex:3229-3258`):
   - `geomSteinOp (p : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ := (1 - p) * fwdDiff 1 f k - p * f k + p * f 0`.
   - `geomSteinSol (p : ℝ) (A : Set ℕ) (k : ℕ) : ℝ` is the canonical solution $f_A(k) = \sum_{i \in A} (1 - p)^i - \sum_{i \in A,\, i \ge k} (1 - p)^{i - k}$ of $(1 - p)\Delta f_A(k) - p f_A(k) = \mathbf{1}_{k \in A} - \mathrm{Ge}^0(p)(A)$ with $f_A(0) = 0$.
   - `geomSteinClass : Set (ℕ → ℝ) := {f | f 0 = 0 ∧ ∀ k : ℕ, |fwdDiff 1 f k| ≤ 1}`.
3. **`SteinMethod.IsDiscreteEquilibrium`** (Definition 6.1, eq. `(6.1)` `\label {1717}`, `SteinIntro.tex:3283-3289`):
   - `IsDiscreteEquilibrium P p W P' We` asserts `0 < p ∧ p ≤ 1`, `AEMeasurable W P`, `Integrable (fun ω ↦ (W ω : ℝ)) P`, `∫ ω, (W ω : ℝ) ∂P = (1 - p) / p`, `AEMeasurable We P'`, and `p * (∫ ω, f (W ω) ∂P) - p * f 0 = (1 - p) * ∫ ω', fwdDiff 1 f (We ω') ∂P'` for all `f : ℕ → ℝ` with bounded forward difference `∃ C : ℝ, ∀ k : ℕ, |fwdDiff 1 f k| ≤ C`.
4. **`SteinMethod.uniformAttachment`, `SteinMethod.digraphOfTargets`, and `SteinMethod.digraphInDegree`** (`SteinIntro.tex:3334-3341`):
   - `Digraph V` carries `instMeasurableSpaceDigraph := .comap Digraph.Adj inferInstance`.
   - `uniformAttachment (n : ℕ) : Measure (Digraph (Fin n))` pushes forward independent uniform attachment target choices `∀ k : Fin n, Fin (k.val + 1)` via `digraphOfTargets` (`Adj u v := (t u).val = v.val`), and `digraphInDegree G v := {u : V | G.Adj u v}.ncard` counts the initial self-loop at node `0` once toward in-degree per `SteinIntro.tex:3335-3336`.

---

## 7. Poisson Local Dependence & Head Runs (`Formalization/Defs/PoissonDep.lean`)

1. **`SteinMethod.poissonSteinClass`** (`SteinIntro.tex:1881-1884, 1911-1916`):
   - `poissonSteinClass (r : ℝ≥0) : Set (ℕ → ℝ) := {f | (∀ k, |f k| ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))) ∧ (∀ k, |fwdDiff 1 f k| ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ))}` represents the Chen–Stein function class $\mathcal{F}$ satisfying `(4.2)`. Non-vacuity: `poissonSteinSol_mem_poissonSteinClass` (`Formalization/PoissonDep/Basic.lean`).
2. **`SteinMethod.headRunIndicator` and `SteinMethod.headRunCount`** (`SteinIntro.tex:2013-2023`, Theorem 4.8):
   - `headRunIndicator {n : ℕ} (k : ℕ) (y : Fin n → ℕ) (i : ℕ) : ℕ` is the `0`-indexed de-clumped indicator ($i \in \{0, \dots, n - k\}$) that a head run of length $\ge k$ begins at position $i$ ($1$ at $i = 0$ when $\prod_{j < k} y_j = 1$, and $(1 - y_{i - 1}) \prod_{j < k} y_{i + j}$ for $i \ge 1$, returning $0$ if $k = 0$ or $n < i + k$).
   - `headRunCount {n : ℕ} (k : ℕ) (y : Fin n → ℕ) : ℕ := ∑ i ∈ Finset.range (n - k + 1), headRunIndicator k y i` (for $1 \le k \le n$, `0` otherwise).
3. **`SteinMethod.longestQualityRun` and `SteinMethod.klDivBernoulli`** (`SteinIntro.tex:2055, 2066-2078`, Theorem 4.9):
   - `longestQualityRun {n : ℕ} (a : ℝ) (y : Fin n → ℕ) : ℕ` returns the greatest $j \in \{0, \dots, n\}$ such that $\sum_{r < j} y_{i + r} \ge a j$ for some $i$ with $i + j \le n$.
   - `klDivBernoulli (a p : ℝ) : ℝ := if a = 1 then Real.log (1 / p) else a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))` encodes the binary relative entropy $H(a, p)$ in Erdős–Rényi's Law.
