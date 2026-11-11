/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 3 Statements (`Formalization.Statements.Sec3`)

Self-contained theorem, proposition, lemma, remark, and example statements from Section 3 of
Nathan Ross, *"Fundamentals of Stein's method"* (`SteinIntro.tex:700-1815`), importing core
definitions only (`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace SteinMethod

/-- Section 3 Kolmogorov–Wasserstein normal comparison (`SteinIntro.tex:703-707`): for any
real-valued random variable $W$ and standard normal $Z \sim \mathcal{N}(0, 1)$,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
(2 / \pi)^{1/4} \sqrt{d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))}$. -/
def Sec3_dK_le_dW : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    AEMeasurable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) *
        wassersteinDist (P.map W) (P'.map Z) ^ (1 / 2 : ℝ)

/-- Theorem 3.1 (`\label{thm31}`, eq. `(3.2)` `\label{35}`, `SteinIntro.tex:719-724`; `D6` literal
class): for any real-valued random variable $W$ and standard normal $Z \sim \mathcal{N}(0, 1)$,
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]|$. -/
def Thm3_1 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    AEMeasurable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|

/-- Theorem 3.2 (`\label{thm32}`, `SteinIntro.tex:736-742`): Wasserstein normal approximation bound
for $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ when $X_1, \dots, X_n$ are independent random variables with
$\mathbb{E}|X_i|^4 < \infty$, $\mathbb{E}[X_i] = 0$, and $\mathbb{E}[X_i^2] = 1$. -/
def Thm3_2 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P))

/-- Lemma 3.3 (`\label{lem33}`, eqs. `(3.3)`–`(3.4)` `\label{345}`–`\label{345a}`,
`SteinIntro.tex:753-759`; `ISSUE-TYPO-3.3`, `ISSUE-3.3`): leave-one-out Stein expansion for
$W = (\sum_{i=1}^n X_i)/\sqrt{n}$ and $W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$. -/
def Lem3_3 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {f : ℝ → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    Differentiable ℝ f →
    (∃ B₀ : ℝ, ∀ w : ℝ, |f w| ≤ B₀) →
    (∃ B₁ : ℝ, ∀ w : ℝ, |deriv f w| ≤ B₁) →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
    ∫ ω, W ω * f (W ω) ∂P =
      (∫ ω, (1 / Real.sqrt n) * ∑ i : Fin n,
          X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P) +
        ∫ ω, (1 / Real.sqrt n) * ∑ i : Fin n,
          X i ω * (W ω - W_i i ω) * deriv f (W ω) ∂P

/-- Lemma 3.4 (`\label{lem33aa}`, eq. `(3.6)` `\label{337}`, `SteinIntro.tex:771-776`): bound on
$|\mathbb{E}[f'(W) - W f(W)]|$ for $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ when $f$ is bounded with
bounded first and second derivatives. -/
def Lem3_4 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {f : ℝ → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    (Differentiable ℝ f ∧ Differentiable ℝ (deriv f)) →
    (∃ B₀ : ℝ, ∀ w : ℝ, |f w| ≤ B₀) →
    ∀ {B₁ B₂ : ℝ},
      (∀ w : ℝ, |deriv f w| ≤ B₁) →
      (∀ w : ℝ, |deriv (deriv f) w| ≤ B₂) →
      let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
      |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          B₁ / (n : ℝ) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P)

/-- Theorem 3.5, corrected (`\label{thm41}`, eq. `(3.8)` `\label{41}`, `SteinIntro.tex:815-822`;
`ISSUE-3.5`): Wasserstein normal approximation bound for $W = (\sum_{i=1}^n X_i)/\sigma$ under
`IsDependencyGraph P X N` and $\sigma^2 = \operatorname{Var}(\sum_i X_i) > 0$. The hypothesis is
strengthened from dependency neighbourhoods (Definition 3.1) to a dependency graph, because the
printed theorem is false (`not_Thm3_5_printed`, `ISSUE-3.5`). -/
def Thm3_5_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)} {Z : Ω' → ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    IsDependencyGraph P X N →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
    let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (D ^ 2 / σ ^ 3 * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P))

/-- Section 3.2.1 application, restricted (`SteinIntro.tex:918-949`; `ISSUE-TYPO-3.2.1`,
`ISSUE-3.2.1`): for triangle counts $T$ in $G(n, p)$ with $n \ge 3$ and $0 < p < 1$,
$\mathbb{E}[T] = \binom{n}{3} p^3$, $\sigma^2 = \operatorname{Var}(T) = \binom{n}{3} p^3
[1 - p^3 + 3(n - 3)p^2(1 - p)]$, and $W = (T - \mathbb{E}[T])/\sigma$ satisfies the Theorem 3.5
Wasserstein bound (printed with $\dk$ by typo at `SteinIntro.tex:936`, `ISSUE-TYPO-3.2.1`, and
restricted from $0 \le p \le 1$ at `SteinIntro.tex:941` because $\sigma = 0$ at $p \in \{0, 1\}$,
`ISSUE-3.2.1`). The printed inequality for $d_{\mathrm{K}}$ is not established here; this entry
proves the bound for $d_{\mathrm{W}}$, which is what Theorem 3.5 yields. -/
def Sec3_2_1_triangles_restricted : Prop :=
  ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {Z : Ω' → ℝ},
    3 ≤ n →
    0 < p →
    p < 1 →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℝ := ∫ G, T G ∂erdosRenyi n p
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance T (erdosRenyi n p))
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (T G - μ) / σ
    μ = (n.choose 3 : ℝ) * p ^ 3 ∧
      ProbabilityTheory.variance T (erdosRenyi n p) =
        (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) ∧
      wassersteinDist ((erdosRenyi n p).map W) (P'.map Z) ≤
        ENNReal.ofReal
          ((3 * (n : ℝ) - 8) ^ 2 / σ ^ 3 *
              ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6)) +
            Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
              (Real.sqrt Real.pi * σ ^ 2) *
              Real.sqrt
                ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9)))

/-- Section 3.2.1 Ruciński triangle-count CLT criterion (`SteinIntro.tex:943-944`, citing
Ruciński 1988 `\cite{ruc88}`, Theorem 2 specialized to $H = K_3$ with
$m(K_3) = e(K_3)/v(K_3) = 1$, proved from scratch): for $G \sim G(n, p_n)$ with $0 \le p_n \le 1$,
the standardized triangle count $W_n = (T_n - \mathbb{E}[T_n]) / \sigma_n$ converges in
distribution to $\mathcal{N}(0, 1)$ (equivalently pointwise in CDF, in Kolmogorov distance
$d_{\mathrm{K}}$, or in Wasserstein distance $d_{\mathrm{W}}$) if and only if $n p_n \to \infty$
and $n^2 (1 - p_n) \to \infty$.

Convention note: when $\sigma_n = 0$ (e.g. $p_n \in \{0, 1\}$ or $n < 3$), Lean's real division
evaluates $W_n = 0$; the full domain $0 \le p_n \le 1$ is sound without $0 < p_n < 1$ because if
$p_n \in \{0, 1\}$ infinitely often then $W_n \equiv 0$ along that subsequence (so normal
convergence fails) while $n p_n = 0$ or $n^2 (1 - p_n) = 0$ along that subsequence (so the
criterion also fails), whereas $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$ force
$0 < p_n < 1$ and $\sigma_n > 0$ eventually. -/
def Sec3_2_1_triangles_rucinski : Prop :=
  ∀ {p : ℕ → ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    ((∀ x : ℝ,
        Filter.Tendsto
          (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          Filter.atTop (nhds (stdNormalCDF x))) ↔
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) Filter.atTop Filter.atTop) ∧
    (Filter.Tendsto
        (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) Filter.atTop Filter.atTop) ∧
    (Filter.Tendsto
        (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) Filter.atTop Filter.atTop)

/-- Section 3.2.1 power-law normal-convergence regime (`SteinIntro.tex:942-944`, citing
Ruciński 1988 `\cite{ruc88}`, Theorem 2 with $m(K_3) = 1$, proved from scratch): if
$0 \le p_n \le 1$ satisfies $\lim_{n \to \infty} n^\alpha p_n = c > 0$ for some $\alpha \ge 0$,
with $c < 1$ when $\alpha = 0$ (excluding the $p_n \to 1$ boundary, `ISSUE-3.2.1`), then:
1. for every $0 \le \alpha < 1$ (strictly containing the dependency-neighborhood regime
   $0 \le \alpha < 2/9$, since on $[2/9, 1)$ the Section 3.2.1 Stein upper bound fails to vanish),
   $W_n = (T_n - \mathbb{E}[T_n])/\sigma_n$ converges to $\mathcal{N}(0, 1)$ in Wasserstein
   distance, Kolmogorov distance, and pointwise CDF;
2. conversely, for $\alpha \ge 1$, normal convergence fails in pointwise CDF, $d_{\mathrm{K}}$,
   and $d_{\mathrm{W}}$.

Convention note: when $\sigma_n = 0$, Lean's real division sets $W_n = 0$; for $0 \le \alpha < 1$
with $c > 0$ (and $c < 1$ when $\alpha = 0$), $0 < p_n < 1$ and $\sigma_n > 0$ hold eventually. -/
def Sec3_2_1_triangles_rucinski_power_regime : Prop :=
  ∀ {p : ℕ → ℝ} {α c : ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    0 ≤ α →
    0 < c →
    (α = 0 → c < 1) →
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) Filter.atTop (nhds c) →
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    (α < 1 →
      Filter.Tendsto
        (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ∧
      (∀ x : ℝ,
        Filter.Tendsto
          (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          Filter.atTop (nhds (stdNormalCDF x)))) ∧
    (1 ≤ α →
      ¬ (∀ x : ℝ,
          Filter.Tendsto
            (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
            Filter.atTop (nhds (stdNormalCDF x))) ∧
      ¬ Filter.Tendsto
          (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          Filter.atTop (nhds 0) ∧
      ¬ Filter.Tendsto
          (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          Filter.atTop (nhds 0))

/-- Proposition 3.6(1) (`\label{prop51}`, `SteinIntro.tex:962-971`): if $(W, W')$ is an
exchangeable pair of real-valued random variables and $F : \mathbb{R}^2 \to \mathbb{R}$ is
antisymmetric ($F(x, y) = -F(y, x)$), then $\mathbb{E}[F(W, W')] = 0$.

No integrability hypothesis is imposed on $F(W, W')$; `Measurable F` is the typing of a measurable
function `ℝ × ℝ → ℝ`. -/
def Prop3_6_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℝ} {F : ℝ × ℝ → ℝ},
    IsExchangeablePair P W W' →
    Measurable F →
    (∀ x y : ℝ, F (x, y) = -F (y, x)) →
    ∫ ω, F (W ω, W' ω) ∂P = 0

/-- Proposition 3.6(2) (`\label{prop51}`, `SteinIntro.tex:967-971`): if $(W, W')$ is an
$a$-Stein pair with finite second moment (`MemLp W 2 P`), then $\mathbb{E}[W] = 0$ and
$\mathbb{E}[(W' - W)^2] = 2 a \operatorname{Var}(W)$. -/
def Prop3_6_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ},
    IsSteinPair P a W W' →
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 0 ∧ ∫ ω, (W' ω - W ω) ^ 2 ∂P = 2 * a * ProbabilityTheory.variance W P

/-- Theorem 3.7 (`\label{thm51}`, `SteinIntro.tex:983-988`): if $(W, W')$ is an $a$-Stein pair
with $\mathbb{E}[W^2] = 1$ and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{\sqrt{2\pi}\,a} +
\frac{\mathbb{E}|W' - W|^3}{3a}$, with extended-nonnegative-real moments (`evariance`,
`lintegral`). -/
def Thm3_7 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ},
    IsSteinPair P a W W' →
    ∫ ω, W ω ^ 2 ∂P = 1 →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (Real.sqrt (2 * Real.pi) * a) +
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * a)

/-- Remark 3.3 (`SteinIntro.tex:990-999`): if a Markov kernel $\kappa$ is reversible with respect
to a probability measure $\mu$ (`(μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ`), then for any measurable
statistic $W$, $(W(X_0), W(X_1))$ is exchangeable under $\mu \otimes_{\mathrm{m}} \kappa$. -/
def Rem3_3 : Prop :=
  ∀ {𝒳 α : Type*} [MeasurableSpace 𝒳] [MeasurableSpace α]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel 𝒳 𝒳) [ProbabilityTheory.IsMarkovKernel κ]
    {W : 𝒳 → α},
    (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ →
    Measurable W →
    IsExchangeablePair (μ ⊗ₘ κ) (fun p ↦ W p.1) (fun p ↦ W p.2)

/-- Remark 3.4 (`SteinIntro.tex:1000-1008`): for sub-$\sigma$-algebras $m_1 \le m_2$ of the ambient
$\sigma$-algebra and any integrable random variable $Y$,
$\operatorname{Var}(\mathbb{E}[Y \mid m_1]) \le \operatorname{Var}(\mathbb{E}[Y \mid m_2])$ in
`ℝ≥0∞` (`ProbabilityTheory.evariance`). -/
def Rem3_4 : Prop :=
  ∀ {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} {Y : Ω → ℝ},
    m₁ ≤ m₂ →
    m₂ ≤ m₀ →
    Integrable Y P →
    ProbabilityTheory.evariance (P[Y | m₁]) P ≤
      ProbabilityTheory.evariance (P[Y | m₂]) P

/-- Example 3.6, Stein-pair verification (`SteinIntro.tex:1053-1069`): for independent centered
unit-variance random variables $X_1, \dots, X_n$ with $\mathbb{E}[X_i^4] < \infty$, an independent
copy $(X_1', \dots, X_n')$, and an independent uniform random index $I \in \{1, \dots, n\}$,
$(W, W')$ with $W = n^{-1/2}\sum_i X_i$ and $W' = W - X_I/\sqrt{n} + X_I'/\sqrt{n}$ is a
$(1/n)$-Stein pair. -/
def Ex3_6_steinPair : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    IsSteinPair P (1 / (n : ℝ)) W W'

/-- Example 3.6, corrected Wasserstein bound (`SteinIntro.tex:1053-1097`; `ISSUE-3.6`): for all
$n \ge 1$, applying Theorem 3.7 to the $(1/n)$-Stein pair $(W, W')$ yields second term
$\frac{8}{3 n^{3/2}} \sum_{i=1}^n \mathbb{E}|X_i|^3$. The printed second term is
$\frac{2}{3n} \sum_{i=1}^n \mathbb{E}|X_i|^3$ (`SteinIntro.tex:1089`), and it is replaced here by
$\frac{8}{3 n^{3/2}} \sum_{i=1}^n \mathbb{E}|X_i|^3$ (`ISSUE-3.6`). -/
def Ex3_6_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n} {Z : Ω' → ℝ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Example 3.6, restricted printed Wasserstein bound (`SteinIntro.tex:1053-1097`, `L1089`;
`ISSUE-3.6`): for $n \ge 16$, $\frac{8}{3 n^{3/2}} \le \frac{2}{3n}$, so the printed bound holds
with second term $\frac{2}{3n} \sum_{i=1}^n \mathbb{E}|X_i|^3$. -/
def Ex3_6_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n} {Z : Ω' → ℝ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    16 ≤ n →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Example 3.6, printed Wasserstein bound (`SteinIntro.tex:1053-1097`, `L1089`; `ISSUE-3.6`):
for all $n \ge 1$ and independent mean-zero, unit-variance random variables
$X_1, \dots, X_n \in L^4(P)$, $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ satisfies the printed bound
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sqrt{\frac{2}{\pi}}\frac{\sqrt{\sum_{i=1}^n \mathbb{E}[X_i^4]}}{2n} +
\frac{2}{3n}\sum_{i=1}^n \mathbb{E}|X_i|^3$. -/
def Ex3_6_printed : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Section 3.3.1 anti-voter ergodicity and stationary uniqueness, corrected
(`SteinIntro.tex:1101-1111`, citing Aldous–Fill `[af10]`; `ISSUE-3.8`): if $G$ is a connected
$r$-regular finite simple graph that is neither bipartite nor isomorphic to `cycleGraph |V|`, then:
1. Every one-step transition of `antiVoterStep G` lands in the absorbing set of non-constant
   labelings $\mathcal{N}(V) = \{x : V \to \mathrm{Bool} \mid
   (\exists a, x_a = \mathrm{true}) \wedge (\exists b, x_b = \mathrm{false})\}$;
2. On $\mathcal{N}(V)$, the anti-voter Markov chain is irreducible and aperiodic
   ($\forall x, y \in \mathcal{N}(V), \exists N, \forall t \ge N, P^t(x, y) > 0$);
3. The anti-voter chain on `V → Bool` has a unique stationary probability distribution, whose
   support is $\mathcal{N}(V)$.

Deviations from the printed claim at `SteinIntro.tex:1110-1111` (`ISSUE-3.8`):
1. Irreducibility and aperiodicity are stated on the absorbing set $\mathcal{N}(V)$ of non-constant
   labelings rather than on the full space $\{-1, 1\}^V$ (constant labelings have zero incoming
   transition probability);
2. `G.Connected` is added (`ISSUE-3.8`; omitted in the printed text, where stationary uniqueness on
   $\{-1, 1\}^V$ is refuted without connectedness by $G = K_3 \sqcup C_4$ in
   `not_Sec3_3_1_antiVoter_unique_printed` / `antiVoter_disconnected_counterexample`);
3. `G.IsRegularOfDegree r` is retained in this index entry to match the printed §3.3.1 setting,
   while the underlying library theorem `antiVoter_ergodic_and_unique_stationary` drops
   $r$-regularity altogether (strengthening the result to arbitrary connected finite simple graphs
   that are neither bipartite nor cycles). -/
def Sec3_3_1_antiVoter_ergodic_corrected : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ},
    G.IsRegularOfDegree r →
    G.Connected →
    ¬ G.IsBipartite →
    IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) →
    (∀ ⦃x y : V → Bool⦄,
      antiVoterStep G x y ≠ 0 →
      (∃ a : V, y a = true) ∧ (∃ b : V, y b = false)) ∧
    (∀ ⦃x y : V → Bool⦄,
      ((∃ a : V, x a = true) ∧ (∃ b : V, x b = false)) →
      ((∃ a : V, y a = true) ∧ (∃ b : V, y b = false)) →
      ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
        0 < ((fun p : PMF (V → Bool) ↦ p.bind (antiVoterStep G))^[t] (PMF.pure x)) y) ∧
    (∃ ν : Measure (V → Bool),
      IsProbabilityMeasure ν ∧
      IsAntiVoterStationary G ν ∧
      (∀ x : V → Bool,
        ν {x} ≠ 0 ↔ (∃ a : V, x a = true) ∧ (∃ b : V, x b = false)) ∧
      ∀ μ : Measure (V → Bool),
        IsProbabilityMeasure μ → IsAntiVoterStationary G μ → μ = ν)

/-- Theorem 3.8 (`\label{thm52}`, `SteinIntro.tex:1114-1127`): for the anti-voter Markov chain on
an $r$-regular finite simple graph $G$ on $n = |V|$ vertices that is neither bipartite nor a cycle,
if $X$ has a stationary distribution and $X'$ is one step of the chain from $X$, then $(W, W')$ is
a $(2/n)$-Stein pair and $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \frac{4n}{3\sigma^3} +
\frac{\sqrt{\operatorname{Var}(Q)}}{r\sigma^2\sqrt{2\pi}}$. -/
def Thm3_8 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X X' : Ω → V → Bool} {Z : Ω' → ℝ},
    G.IsRegularOfDegree r →
    ¬ G.IsBipartite →
    IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) →
    Measurable X →
    Measurable X' →
    IsAntiVoterStationary G (P.map X) →
    (∀ x y : V → Bool, P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let n : ℝ := Fintype.card V
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    let S' : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X' ω v)
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    let W' : Ω → ℝ := fun ω ↦ S' ω / σ
    let Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
    IsSteinPair P (2 / n) W W' ∧
      wassersteinDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (4 * n / (3 * σ ^ 3) +
            Real.sqrt (ProbabilityTheory.variance Q P) /
              ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi)))

/-- Lemma 3.9 (`\label{lem51}`, `SteinIntro.tex:1133-1136`): if $W$ and $W'$ are identically
distributed integer-valued random variables defined on the same probability space such that
$\mathbb{P}(|W' - W| \le 1) = 1$, then $(W, W')$ is an exchangeable pair. -/
def Lem3_9 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℤ},
    ProbabilityTheory.IdentDistrib W W' P P →
    (∀ᵐ ω ∂P, |W' ω - W ω| ≤ 1) →
    IsExchangeablePair P W W'

/-- Lemma 3.10 (`SteinIntro.tex:1208-1214`): for any stationary distribution of the anti-voter
Markov chain on an $r$-regular finite simple graph $G$ ($r > 0$), the variance $\sigma^2$ of the
total spin $S = \sum_{v \in V} \operatorname{spin}(X_v)$ satisfies
$\frac{2 \kappa(G)}{r} \le \sigma^2 \le |V|$. -/
def Lem3_10 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → V → Bool},
    G.IsRegularOfDegree r →
    0 < r →
    Measurable X →
    IsAntiVoterStationary G (P.map X) →
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    2 * (kappa G : ℝ) / (r : ℝ) ≤ ProbabilityTheory.variance S P ∧
      ProbabilityTheory.variance S P ≤ (Fintype.card V : ℝ)

/-- Section 3.4 size-bias Stein identity (eq. `(3.23)` `\label{71}`, `SteinIntro.tex:1232-1236`;
`ISSUE-TYPO-3.4a`): for $X \ge 0$ a.s. in $L^2$ with $\sigma^2 = \operatorname{Var}(X) > 0$,
$\mu = \mathbb{E}[X]$, $W = (X - \mu)/\sigma$, and size-bias $X^s$ on the same space, if $f(W)$ and
$X f(W)$ are integrable then $f((X^s - \mu)/\sigma)$ is integrable and
$\mathbb{E}[W f(W)] = \frac{\mu}{\sigma}(\mathbb{E}[f((X^s - \mu)/\sigma)] - \mathbb{E}[f(W)])$. -/
def Sec3_4_sizeBias_identity : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xs : Ω → ℝ} {f : ℝ → ℝ},
    0 ≤ᵐ[P] X →
    MemLp X 2 P →
    0 < ProbabilityTheory.variance X P →
    IsSizeBias P X P Xs →
    Measurable f →
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    let W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
    Integrable (fun ω ↦ X ω * f (W ω)) P →
    Integrable (fun ω ↦ f (W ω)) P →
    Integrable (fun ω ↦ f ((Xs ω - μ) / σ)) P ∧
      ∫ ω, W ω * f (W ω) ∂P =
        μ / σ * ((∫ ω, f ((Xs ω - μ) / σ) ∂P) - ∫ ω, f (W ω) ∂P)

/-- Proposition 3.11, restricted to $\mu > 0$ (`SteinIntro.tex:1239-1245`; `ISSUE-3.11`, `D8`):
for $X \ge 0$ a.s. integrable with $\mu = \mathbb{E}[X] > 0$, every size-bias random variable $X^s$
has law $dF^s(x) = \frac{x}{\mu}\,dF(x)$, and conversely this weighted measure is a probability
measure whose identity map has the size-bias distribution with respect to $X$. -/
def Prop3_11_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ},
    0 ≤ᵐ[P] X →
    Integrable X P →
    0 < ∫ ω, X ω ∂P →
    let μ : ℝ := ∫ ω, X ω ∂P
    (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {Xs : Ω' → ℝ},
        IsSizeBias P X P' Xs →
        P'.map Xs = (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))) ∧
      (let ν : Measure ℝ := (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))
       IsProbabilityMeasure ν ∧ IsSizeBias P X ν id)

/-- Corollary 3.12, restricted to $\mu > 0$ (`SteinIntro.tex:1246-1252`; `ISSUE-3.11`): if $X \ge 0$
is a nonnegative integer-valued integrable random variable with $\mu = \mathbb{E}[X] > 0$ and $X^s$
has the size-bias distribution of $X$, then $\mathbb{P}(X^s = k) = \frac{k\,\mathbb{P}(X = k)}{\mu}$
for all $k \in \mathbb{N}$. -/
def Cor3_12_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ},
    (∀ᵐ ω ∂P, X ω ∈ Set.range (Nat.cast : ℕ → ℝ)) →
    Integrable X P →
    0 < ∫ ω, X ω ∂P →
    IsSizeBias P X P' Xs →
    let μ : ℝ := ∫ ω, X ω ∂P
    ∀ k : ℕ, P'.real {ω' | Xs ω' = k} = (k : ℝ) * P.real {ω | X ω = k} / μ

/-- Theorem 3.13 (`\label{thm71}`, `SteinIntro.tex:1255-1261`): Wasserstein normal approximation
bound via size-bias coupling on the same probability space, with extended-nonnegative-real moments
(`evariance`, `lintegral`). -/
def Thm3_13 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X Xs : Ω → ℝ} {Z : Ω' → ℝ},
    Measurable X →
    0 ≤ᵐ[P] X →
    MemLp X 2 P →
    0 < ProbabilityTheory.variance X P →
    IsSizeBias P X P Xs →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    let W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
          ProbabilityTheory.evariance
            (P[fun ω ↦ Xs ω - X ω | MeasurableSpace.comap X inferInstance]) P ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (μ / σ ^ 3) * ∫⁻ ω, ENNReal.ofReal ((Xs ω - X ω) ^ 2) ∂P

/-- Proposition 3.14 (`\label{prop71}`, `SteinIntro.tex:1284-1299`): size-bias coupling recipe for
a sum $X = \sum_{i=1}^n X_i$ of nonnegative integrable random variables with total mean
$\mu = \sum_i \mu_i > 0$. -/
def Prop3_14 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, 0 ≤ᵐ[P] X i) →
    (∀ i : Fin n, Integrable (X i) P) →
    0 < (∑ i : Fin n, ∫ ω, X i ω ∂P) →
    (∀ i : Fin n, IsSizeBias P (X i) P (Xs i)) →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      P.map (fun ω ↦ (Xs i ω, Y i ω)) =
        (P.map (Xs i)) ⊗ₘ
          ProbabilityTheory.condDistrib (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) (X i) P) →
    Measurable I →
    (∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P) →
    ProbabilityTheory.IndepFun I
      (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω, fun i ↦ Y i ω)) P →
    let Xs_total : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + Xs (I ω) ω
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P Xs_total

/-- Corollary 3.15 (`\label{cor71}`, `SteinIntro.tex:1319-1325`; `ISSUE-TYPO-3.15`): size-bias
coupling $X^s = X - X_I + X_I^s$ for a sum of independent nonnegative integrable random variables
$X_1, \dots, X_n$ with $\mu = \sum_i \mathbb{E}[X_i] > 0$. -/
def Cor3_15 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, 0 ≤ᵐ[P] X i) →
    (∀ i : Fin n, Integrable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, IsSizeBias P (X i) P (Xs i)) →
    (∀ i : Fin n,
      ProbabilityTheory.IndepFun (Xs i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P) →
    Measurable I →
    (∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)) P →
    0 < (∑ i : Fin n, ∫ ω, X i ω ∂P) →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ i : Fin n, X i ω) - X (I ω) ω + Xs (I ω) ω)

/-- Corollary 3.16 (`\label{cor72}`, `SteinIntro.tex:1326-1332`): size-bias coupling
$X^s = \sum_{j \ne I} X_j^{(I)} + 1$ for a sum of zero-one random variables $X_1, \dots, X_n$ with
$p_i = \mathbb{P}(X_i = 1)$ and $\mu = \sum_i p_i > 0$. -/
def Cor3_16 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    let p : Fin n → ℝ := fun i ↦ P.real (X i ⁻¹' {1})
    let μ : ℝ := ∑ i : Fin n, p i
    0 < μ →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P (X i ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / μ) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1)

/-- Example 3.8 (`\label{ex71}`, `SteinIntro.tex:1349-1353`; Backlog item 9): Ross prints no
formula in Example 3.8 and leaves the derivation as an exercise; this bound is the project's
solution of that exercise, combining Corollary 3.15 (`\label{cor71}`), Theorem 3.13
(`\label{thm71}`), and Remark 3.4 under the independent size-bias coupling ($X_i^s$ independent of
$X$ and mixture index $I$ with $\mathbb{P}(I = i) = \mu_i / \mu$, constructed on an enlarged
product space). Reading notes: (1) nonnegativity (`0 ≤ᵐ[P] X i`) comes from Corollary 3.15's
setting (size-bias requires $X_i \ge 0$), not from the exercise's wording; (2) Ross gives no
formula, so the right-hand side is the project's explicit solution of the exercise; (3)
$\sigma^2 = \operatorname{Var}(\sum_i X_i) > 0$ is typing. -/
def Ex3_8 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    (∀ i : Fin n, 0 ≤ᵐ[P] X i) →
    (∀ i : Fin n, MemLp (X i) 3 P) →
    ProbabilityTheory.iIndepFun X P →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / σ ^ 2 *
            Real.sqrt
              (2 / Real.pi *
                ∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) +
          1 / σ ^ 3 *
            ∑ i : Fin n, ((∫ ω, X i ω ^ 3 ∂P) - (∫ ω, X i ω ∂P) * ∫ ω, X i ω ^ 2 ∂P))

/-- Example 3.9, size-bias realization and increment identity (`\label{ex72}`,
`SteinIntro.tex:1354-1367, 1380-1383`): for $G \sim G(n, p)$ ($n \ge 1$, $0 \le p < 1$) and an
independent uniform vertex $I \in \{1, \dots, n\}$, erasing all edges incident to $I$
(`SimpleGraph.deleteIncidenceSet`) yields a size-bias version $X^s$ of the isolated-vertex count
$X = \sum_{i=1}^n X_i$ (via Corollary 3.16), with increment $X^s - X = D_I + \mathbf{1}_{d_I > 0}$,
where $d_i$ is the degree of $i$ in $G$ and $D_i$ is the number of degree-one neighbors of $i$. -/
def Ex3_9_sizeBias : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {I : Ω → Fin n},
    0 ≤ p →
    p < 1 →
    Measurable G →
    P.map G = erdosRenyi n p →
    Measurable I →
    ProbabilityTheory.IndepFun I G P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i (G ω)
    let Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i ((G ω).deleteIncidenceSet (I ω))
    let d : Fin n → Ω → ℕ := fun i ω ↦ ((G ω).neighborSet i).ncard
    let D : Fin n → Ω → ℝ :=
      fun i ω ↦ ({j : Fin n | (G ω).Adj i j ∧ ((G ω).neighborSet j).ncard = 1}.ncard : ℝ)
    IsSizeBias P X P Xs ∧
      ∀ ω : Ω, Xs ω - X ω = D (I ω) ω + {ω' : Ω | 0 < d (I ω') ω'}.indicator 1 ω

/-- Example 3.9, verified moment formulas (`\label{ex72}`, `SteinIntro.tex:1370-1379, 1406-1409`,
eq. `\label{77}`; see `ISSUE-3.9` for the false printed formulas at `L1395` and `L1397`): for
$G \sim G(n, p)$ with $0 \le p \le 1$, $\mu = \mathbb{E}[X] = n(1 - p)^{n - 1}$,
$\mathbb{E}[X_i X_j] = (1 - p)^{2n - 3}$ ($i \ne j$),
$\sigma^2 = \operatorname{Var}(X) = \mu[1 + (n p - 1)(1 - p)^{n - 2}]$ ($n \ge 2$), and
$\mathbb{E}[D_i^2] = (n - 1)p(1 - p)^{n - 2} + (n - 1)(n - 2)p^2(1 - p)^{2n - 5}$ ($n \ge 3$). -/
def Ex3_9_moments : Prop :=
  ∀ {n : ℕ} {p : ℝ},
    0 ≤ p →
    p ≤ 1 →
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i G ↦ {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator 1 G
    let X : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ i : Fin n, X_ind i G
    let D : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i G ↦ ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)
    (∫ G, X G ∂erdosRenyi n p = (n : ℝ) * (1 - p) ^ (n - 1)) ∧
      (∀ i j : Fin n, i ≠ j →
        ∫ G, X_ind i G * X_ind j G ∂erdosRenyi n p = (1 - p) ^ (2 * n - 3)) ∧
      (2 ≤ n →
        ProbabilityTheory.variance X (erdosRenyi n p) =
          (n : ℝ) * (1 - p) ^ (n - 1) * (1 + ((n : ℝ) * p - 1) * (1 - p) ^ (n - 2))) ∧
      (3 ≤ n →
        ∀ i : Fin n,
          ∫ G, D i G ^ 2 ∂erdosRenyi n p =
            ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) +
              ((n : ℝ) - 1) * ((n : ℝ) - 2) * p ^ 2 * (1 - p) ^ (2 * n - 5))

/-- Theorem 3.17 (`SteinIntro.tex:1413-1420`, nested inside Example 3.9 `\label{ex72}`): if $X_n$
is the number of isolated vertices in an Erdős–Rényi graph $G(n, p_n)$ ($0 \le p_n \le 1$),
$W_n = (X_n - \mu_n)/\sigma_n$, and $\lim_{n \to \infty} n^\alpha p_n = c \in (0, \infty)$ for some
$1 \le \alpha < 2$, then there exists a constant $C$ such that
$d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \le C / \sigma_n$ for all sufficiently large
$n$ (`∀ᶠ n in Filter.atTop`, the asymptotic reading of the limit hypothesis). -/
def Thm3_17 : Prop :=
  ∀ {p : ℕ → ℝ} {α c : ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    1 ≤ α →
    α < 2 →
    0 < c →
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) Filter.atTop (nhds c) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      let X : SimpleGraph (Fin n) → ℝ :=
        fun G ↦ ∑ i : Fin n, {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator 1 G
      let μ : ℝ := ∫ G, X G ∂erdosRenyi n (p n)
      let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X (erdosRenyi n (p n)))
      let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (X G - μ) / σ
      wassersteinDist ((erdosRenyi n (p n)).map W) stdNormalLaw ≤ ENNReal.ofReal (C / σ)

/-- Section 3.5 fixed-point characterization (`SteinIntro.tex:1450-1451`): a real-valued random
variable $W$ satisfies `IsZeroBias P W P W` ($W$ has the zero-bias distribution with respect to
itself) if and only if the law of $W$ is a centered normal distribution $\mathcal{N}(0, v)$
(`normalLaw 0 v`, including the degenerate case $v = 0$, $\mathcal{N}(0, 0) = \delta_0$). -/
def Sec3_5_zeroBias_fixedPoint : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ},
    AEMeasurable W P →
    (IsZeroBias P W P W ↔ ∃ v : NNReal, P.map W = normalLaw 0 v)

/-- Theorem 3.18 (`\label{thm81}`, `SteinIntro.tex:1454-1461`): if $W$ has mean zero and variance
one, $W^z$ is defined on the same probability space and has the zero-bias distribution with respect
to $W$, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le 2\,\mathbb{E}|W^z - W|$, with the right-hand
expectation in `ℝ≥0∞` (`lintegral`) per the junk-zero rule (`D1`, since $\mathbb{E}|W^z| =
\frac{1}{2}\mathbb{E}|W|^3$ may be $+\infty$ under finite second moment alone). -/
def Thm3_18 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ},
    ProbabilityTheory.variance W P = 1 →
    IsZeroBias P W P Wz →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      2 * ∫⁻ ω, ENNReal.ofReal |Wz ω - W ω| ∂P

/-- Proposition 3.19, corrected (`\label{i81}`, `\label{i82}`, eqs. `(3.31)`–`(3.32)`
`\label{81}`–`\label{82}`, `SteinIntro.tex:1471-1485`; `ISSUE-3.10`, `ISSUE-3.19`, ruling `D9`):
for a mean-zero $L^2$ random variable $W$ with strictly positive variance
$\sigma^2 = \operatorname{Var}(W) > 0$,
(1) `zeroBiasDensity P W` satisfies the equivalent left-tail formula
$p^z(w) = -\sigma^{-2}\mathbb{E}[W\mathbf{1}_{W \le w}] \ge 0$,
(2) every zero-bias random variable $W^z$ has law `volume.withDensity (ENNReal.ofReal ∘ p^z)`
(uniqueness + Lebesgue absolute continuity), and
(3) `volume.withDensity (ENNReal.ofReal ∘ p^z)` is a probability measure whose identity map has
the zero-bias distribution with respect to $W$ (existence). -/
def Prop3_19_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ},
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 0 →
    0 < ProbabilityTheory.variance W P →
    (∀ w : ℝ,
        zeroBiasDensity P W w =
          -(ProbabilityTheory.variance W P)⁻¹ *
            ∫ ω, W ω * (Set.Iic w).indicator 1 (W ω) ∂P ∧
          0 ≤ zeroBiasDensity P W w) ∧
      (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {Wz : Ω' → ℝ},
          IsZeroBias P W P' Wz →
          P'.map Wz =
            volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))) ∧
      (let ν : Measure ℝ :=
          volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))
       IsProbabilityMeasure ν ∧ IsZeroBias P W ν id)

/-- Proposition 3.20 (`SteinIntro.tex:1519-1521`, existence reading): if $W$ has mean zero and
finite variance and $W^z$ has the zero-bias distribution of $W$, then for every $a \in \mathbb{R}$
(with no positivity requirement on $\operatorname{Var}(W)$ or $a$), $a W^z$ has the zero-bias
distribution of $a W$. (For distributional uniqueness $(a W)^z \stackrel{d}{=} a W^z$, see
`Prop3_20_restricted` and `ISSUE-3.20`.) -/
def Prop3_20 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    {W : Ω → ℝ} {Wz : Ω' → ℝ} (a : ℝ),
    IsZeroBias P W P' Wz →
    IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω')

/-- Proposition 3.20, restricted to $\operatorname{Var}(W) > 0$ and $a \ne 0$
(`SteinIntro.tex:1519-1521`, law-identity reading; `ISSUE-3.20` as the
$\operatorname{Var}(aW) = a^2\sigma^2 = 0$ instance of `ISSUE-3.19`): if $W$ has mean zero and
$0 < \operatorname{Var}(W) < \infty$, $W^z$ has the zero-bias distribution of $W$, and $a \ne 0$,
then $a W^z$ has the zero-bias distribution of $a W$ and every zero-bias realization $Y$ of $a W$
satisfies $(a W)^z \stackrel{d}{=} a W^z$. -/
def Prop3_20_restricted : Prop :=
  ∀ {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    {W : Ω → ℝ} {Wz : Ω' → ℝ} {Y : Ω'' → ℝ} {a : ℝ},
    0 < ProbabilityTheory.variance W P →
    a ≠ 0 →
    IsZeroBias P W P' Wz →
    IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω') ∧
      (IsZeroBias P (fun ω ↦ a * W ω) P'' Y →
        P''.map Y = P'.map (fun ω' ↦ a * Wz ω'))

/-- Proposition 3.21 (`\label{prop81}`, `SteinIntro.tex:1530-1551`; `ISSUE-TYPO-3.21`): if
$X_1, \dots, X_n$ are independent mean-zero $L^2$ random variables with
$\sum_{i=1}^n \operatorname{Var}(X_i) = 1$, each $X_i^z$ has the zero-bias distribution of $X_i$
and is independent of $(X_j)_{j \ne i}$, and $I$ is an index with $\mathbb{P}(I = i) =
\operatorname{Var}(X_i)$ independent of $((X_i)_i, (X_i^z)_i)$, then
$W^z = \sum_{j \ne I} X_j + X_I^z$ has the zero-bias distribution of $W = \sum_{i=1}^n X_i$.
(Reading note, parallel to `Prop3_14` / `Cor3_15`: Item 1 at `L1533-1534` also mentions
independence of $X_i^z$ from $(X_j^z)_{j \ne i}$, which the proof never uses; assuming only
$X_i^z \perp (X_j)_{j \ne i}$ assumes strictly less and implies the printed proposition.) -/
def Prop3_21 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xz : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (Xz i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 2 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∑ i : Fin n, ProbabilityTheory.variance (X i) P) = 1 →
    (∀ i : Fin n, IsZeroBias P (X i) P (Xz i)) →
    (∀ i : Fin n,
      ProbabilityTheory.IndepFun (Xz i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = ProbabilityTheory.variance (X i) P) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xz i ω)) P →
    IsZeroBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j ∈ Finset.univ.erase (I ω), X j ω) + Xz (I ω) ω)

/-- Section 3.5.2 Lindeberg sufficiency (`SteinIntro.tex:1558-1564`, eq. `(3.34)` `\label{85}`;
`ISSUE-3.22` prose centering note): for a triangular array $(X_{i,n})$ of row-wise independent
mean-zero $L^2$ random variables with $\operatorname{Var}(\sum_i X_{i,n}) = 1$, the Lindeberg
condition `(3.34)` implies $W_n = \sum_i X_{i,n} \xrightarrow{d} \mathcal{N}(0, 1)$ in
`MeasureTheory.ProbabilityMeasure ℝ` (without assuming pre-existing zero-bias or random-index
variables on `Ω`). -/
def Sec3_5_2_lindeberg_sufficient : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (n : ℕ) → Fin (n + 1) → Ω → ℝ},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun n : ℕ ↦
          ∑ i : Fin (n + 1),
            ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
        Filter.atTop (nhds 0)) →
    Filter.Tendsto
      (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      Filter.atTop
      (nhds stdNormalLaw.toProbabilityMeasure)

/-- Section 3.5.2 prose counterexample, corrected (`SteinIntro.tex:1565-1566`;
`ISSUE-3.5.2-PROSE`): taking $X_{1, n} \sim \mathcal{N}(0, 1)$ and $X_{i, n} = 0$ for $i > 1$
gives an independent centered unit-variance triangular array whose row sums $W_n$ converge weakly
to $\mathcal{N}(0, 1)$ yet violate the Lindeberg condition `(3.34)`, showing that `(3.34)` is not
*necessary* for the CLT (printed "not sufficient" by slip of the pen at `L1566`). -/
def Sec3_5_2_lindeberg_not_necessary_corrected : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (X : (n : ℕ) → Fin (n + 1) → Ω → ℝ),
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) ∧
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) ∧
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) ∧
    Filter.Tendsto
      (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      Filter.atTop
      (nhds stdNormalLaw.toProbabilityMeasure) ∧
    ¬ (∀ ε : ℝ, 0 < ε →
        Filter.Tendsto
          (fun n : ℕ ↦
            ∑ i : Fin (n + 1),
              ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
          Filter.atTop (nhds 0))

/-- Theorem 3.22 (`\label{thm82}`, eqs. `(3.34)`–`(3.35)` `\label{85}`–`\label{86}`,
`SteinIntro.tex:1568-1575`; `ISSUE-3.22`): for a triangular array $(X_{i, n})$ of row-wise
independent mean-zero $L^2$ random variables with $\operatorname{Var}(\sum_i X_{i, n}) = 1$, random
index $I_n$ with $\mathbb{P}(I_n = i) = \sigma_{i, n}^2$ independent of $((X_{i, n})_i,
(X_{i, n}^z)_i)$, and zero-bias variables $X_{i, n}^z$, the Lindeberg condition `(3.34)` holds if
and only if $X_{I_n, n}^z \stackrel{p}{\to} 0$ as $n \to \infty$. -/
def Thm3_22 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Xz n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ (n : ℕ) (i : Fin (n + 1)), IsZeroBias P (X n i) P (Xz n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      ProbabilityTheory.IndepFun (Xz n i)
        (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P) →
    (∀ n : ℕ, Measurable (I n)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P) →
    (∀ n : ℕ,
      ProbabilityTheory.IndepFun (I n)
        (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) →
    ((∀ ε : ℝ, 0 < ε →
        Filter.Tendsto
          (fun n : ℕ ↦
            ∑ i : Fin (n + 1),
              ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
          Filter.atTop (nhds 0)) ↔
      MeasureTheory.TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) Filter.atTop 0)

/-- Section 3.5.2 prose claim (`SteinIntro.tex:1585-1586, 1625-1646`): under the hypotheses of
Theorem 3.22, $X_{I_n, n}^z \stackrel{p}{\to} 0$ implies $\max_i \sigma_{i, n}^2 \to 0$ and
$X_{I_n, n} \stackrel{p}{\to} 0$. -/
def Sec3_5_2_zeroBias_imp_tendstoInMeasure : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Xz n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ (n : ℕ) (i : Fin (n + 1)), IsZeroBias P (X n i) P (Xz n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      ProbabilityTheory.IndepFun (Xz n i)
        (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P) →
    (∀ n : ℕ, Measurable (I n)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P) →
    (∀ n : ℕ,
      ProbabilityTheory.IndepFun (I n)
        (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) →
    MeasureTheory.TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) Filter.atTop 0 →
    Filter.Tendsto
        (fun n : ℕ ↦ Finset.univ.sup' Finset.univ_nonempty
          fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) P)
        Filter.atTop (nhds 0) ∧
      MeasureTheory.TendstoInMeasure P (fun n ω ↦ X n (I n ω) ω) Filter.atTop 0

/-- Theorem 3.23 (`\label{thm83}`, `SteinIntro.tex:1578-1581`; `ISSUE-3.22`): in the setting of
Theorem 3.22, if $X_{I_n, n}^z \to 0$ in probability as $n \to \infty$, then $W_n = \sum_i X_{i,n}$
satisfies a central limit theorem, i.e., the laws of $W_n$ converge weakly to `stdNormalLaw` in
`MeasureTheory.ProbabilityMeasure ℝ`. -/
def Thm3_23 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Xz n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ (n : ℕ) (i : Fin (n + 1)), IsZeroBias P (X n i) P (Xz n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      ProbabilityTheory.IndepFun (Xz n i)
        (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P) →
    (∀ n : ℕ, Measurable (I n)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P) →
    (∀ n : ℕ,
      ProbabilityTheory.IndepFun (I n)
        (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) →
    MeasureTheory.TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) Filter.atTop 0 →
    Filter.Tendsto
      (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      Filter.atTop
      (nhds stdNormalLaw.toProbabilityMeasure)

/-- Section 3.6 motivating binomial rate claim (`SteinIntro.tex:1655-1657`): for fixed
$0 < p < 1$, if $W$ is a standardized $\mathrm{Bin}(n, p)$ random variable ($n \ge 1$, represented
as $((\sum_{i=1}^n X_i) - n p) / \sqrt{n p (1 - p)}$ for independent $\{0, 1\}$-valued $X_i$ with
$\mathbb{P}(X_i = 1) = p$) and $Z \sim \mathcal{N}(0, 1)$, then both
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z))$ and
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))$ have two-sided order $n^{-1/2}$ for all
$n \ge 1$. -/
def Sec3_6_binomial_order : Prop :=
  ∀ {p : ℝ},
    0 < p →
    p < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
        1 ≤ n →
        (∀ i : Fin n, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X P →
        (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
        (∀ i : Fin n, P.real (X i ⁻¹' {1}) = p) →
        AEMeasurable Z P' →
        P'.map Z = stdNormalLaw →
        let W : Ω → ℝ :=
          fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
        (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ kolmogorovDist (P.map W) (P'.map Z) ∧
          kolmogorovDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2))) ∧
        (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ wassersteinDist (P.map W) (P'.map Z) ∧
          wassersteinDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2)))

/-- Theorem 3.24, corrected (`\label{thm91}`, eq. `(3.38)` `\label{91}`,
`SteinIntro.tex:1666-1675`; `ISSUE-2.2`, `D4`): if $W$ is a real-valued random variable with finite
mean and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) =
\sup_{x \in \mathbb{R}} |\mathbb{E}[D_- f_x(W) - W f_x(W)]|$, where
$f_x = \mathrm{normalSteinSolKolm}\,x$ solves the left-derivative normal Stein equation
(`ISSUE-2.2`). Per ruling `D4`, the printed finite-mean hypothesis (`Integrable W P`) is retained in
the statement (the library theorem requires only `AEMeasurable W P`). -/
def Thm3_24_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    Integrable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) =
      ⨆ x : ℝ, ENNReal.ofReal |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P|

/-- Lemma 3.25, corrected (`\label{lem91}`, `SteinIntro.tex:1677-1686`; `ISSUE-2.2`, `ISSUE-3.25`,
`D4`): for every $x \in \mathbb{R}$, the Kolmogorov Stein solution
$f_x = \mathrm{normalSteinSolKolm}\,x$ satisfies $|f_x(w)| \le \sqrt{\pi / 2}$,
$|D_- f_x(w)| \le 2$ (using the left derivative at the jump point $w = x$, `ISSUE-2.2`; the sharp
bound $|D_- f_x(w)| \le 1$ also holds and is used in the proof of Theorem 3.28, `ISSUE-3.25`), and
$|(w + u) f_x(w + u) - (w + v) f_x(w + v)| \le (|w| + \sqrt{2\pi}/4)(|u| + |v|)$ for all
$u, v, w \in \mathbb{R}$. -/
def Lem3_25_corrected : Prop :=
  ∀ x : ℝ,
    (∀ w : ℝ, |normalSteinSolKolm x w| ≤ Real.sqrt (Real.pi / 2)) ∧
    (∀ w : ℝ, |derivWithin (normalSteinSolKolm x) (Set.Iic w) w| ≤ 2) ∧
    (∀ u v w : ℝ,
      |(w + u) * normalSteinSolKolm x (w + u) - (w + v) * normalSteinSolKolm x (w + v)| ≤
        (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|))

/-- Corollary 3.26 (`\label{cor91}`, `SteinIntro.tex:1688-1694`): if $\mathcal{F}$ is the class
`normalKolmogorovClass` of differentiable functions satisfying the bounds of Lemma 3.25, $W$ is a
real-valued random variable with finite mean, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]|$.

Reading note: $\mathcal{F}$ (`normalKolmogorovClass`) is read as the *differentiable* functions
satisfying Lemma 3.25's bounds; this excludes $f_x$ itself and gives a smaller supremum, so the
entry implies every weaker-regularity reading (proved by smoothing $\mathbb{I}[\cdot \le x]$ with a
piecewise-linear ramp). -/
def Cor3_26 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    Integrable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ normalKolmogorovClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|

/-- Theorem 3.27 (`SteinIntro.tex:1697-1704`, §3.6.1; `ISSUE-3.10`, `D9`): if $W$ has mean zero and
variance one, $W^z$ has the zero-bias distribution of $W$ on the same probability space with
$|W^z - W| \le \delta$ almost surely, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
(1 + 1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,\delta$. -/
def Thm3_27 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ} {δ : ℝ},
    ProbabilityTheory.variance W P = 1 →
    IsZeroBias P W P Wz →
    (∀ᵐ ω ∂P, |Wz ω - W ω| ≤ δ) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * δ)

/-- Section 3.6.1 zero-bias boundedness inheritance, restricted to positive variance
(`SteinIntro.tex:1741-1742`; `ISSUE-3.19`, `ISSUE-TYPO-3.27`): if $\operatorname{Var}(W) > 0$,
$|W| \le M$ almost surely, and $W^z$ has the zero-bias distribution of $W$, then $|W^z| \le M$
almost surely. (At $\operatorname{Var}(W) = 0$, $W \equiv 0$ admits unbounded zero-bias versions
such as $\mathcal{N}(0, 1)$; see `zero_stdNormalLaw_isZeroBias_unbounded`.) -/
def Sec3_6_zeroBias_bdd_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Wz : Ω' → ℝ} {M : ℝ},
    0 < ProbabilityTheory.variance W P →
    IsZeroBias P W P' Wz →
    (∀ᵐ ω ∂P, |W ω| ≤ M) →
    ∀ᵐ ω' ∂P', |Wz ω'| ≤ M

/-- Section 3.6.1 zero-bias boundedness inheritance, existence reading (`SteinIntro.tex:1741-1742`):
without assuming $\operatorname{Var}(W) > 0$, if $W \in L^2(P)$ has mean zero and $|W| \le M$
almost surely, then there exists a zero-bias law $\nu$ of $W$ supported on $[-M, M]$ (taking
$\nu = \delta_0$ when $\operatorname{Var}(W) = 0$). -/
def Sec3_6_zeroBias_bdd_exists : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {M : ℝ},
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 0 →
    (∀ᵐ ω ∂P, |W ω| ≤ M) →
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ IsZeroBias P W ν id ∧ ∀ᵐ x : ℝ ∂ν, |x| ≤ M

/-- Theorem 3.28 (`\label{thm92}`, `SteinIntro.tex:1750-1755`; `ISSUE-3.25` proof note, `D7`): if
$(W, W')$ is an $a$-Stein pair with $\operatorname{Var}(W) = 1$ and $|W' - W| \le \delta$ almost
surely, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{2a} + \frac{\delta^3}{2a} +
\frac{3\delta}{2}$.

Proof note (`ISSUE-3.25`): obtaining denominator $2a$ in the first term at `SteinIntro.tex:1768`
uses the sharp bound $|D_- f_x(w)| \le 1$ (CGS 2011 Lemma 2.3) rather than the looser bound
$\|f_x'\| \le 2$ printed in Lemma 3.25; the theorem holds as printed. -/
def Thm3_28 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a δ : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ},
    IsSteinPair P a W W' →
    ProbabilityTheory.variance W P = 1 →
    (∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) +
      ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2)

/-- Lemma 3.29 (`\label{lem92}`, `SteinIntro.tex:1793-1798`; `D7`): if $(W, W')$ is an $a$-Stein
pair with $\operatorname{Var}(W) = 1$ and $|W' - W| \le \delta$ almost surely, then for all
$x \in \mathbb{R}$, $\mathbb{E}[(W' - W)^2 \mathbb{I}[x < W \le x + \delta]] \le 3 \delta a$. -/
def Lem3_29 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a δ : ℝ} {W W' : Ω → ℝ} (x : ℝ),
    IsSteinPair P a W W' →
    ProbabilityTheory.variance W P = 1 →
    (∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ) →
    ∫ ω, (W' ω - W ω) ^ 2 * (Set.Ioc x (x + δ)).indicator 1 (W ω) ∂P ≤ 3 * δ * a

end SteinMethod
