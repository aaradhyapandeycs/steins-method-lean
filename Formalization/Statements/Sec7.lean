/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 7 Statements (`Formalization.Statements.Sec7`)

Self-contained theorem, proposition, example, remark, and prose statements from Section 7
(`\label{conc}`, *Concentration of measure*, `SteinIntro.tex:3398-3884`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`), importing core definitions only
(`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace SteinMethod

/-- Proposition 7.1 (`\label{prop211}`, `SteinIntro.tex:3411-3417`): exponential Markov /
Chernoff upper and lower tail inequalities for a real-valued random variable $W$ with
finite moment generating function on $(-\delta, \delta)$. -/
def Prop7_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {δ : ℝ},
    AEMeasurable W P →
    0 < δ →
    (∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * W ω)) P) →
    ∀ {t θ : ℝ},
      0 < t →
      0 < θ →
      θ < δ →
      P.real {ω | t ≤ W ω} ≤ (∫ ω, Real.exp (θ * W ω) ∂P) / Real.exp (θ * t) ∧
        P.real {ω | W ω ≤ -t} ≤ (∫ ω, Real.exp (-θ * W ω) ∂P) / Real.exp (θ * t)

/-- Example 7.1 (`\label{ex211}`, `SteinIntro.tex:3428-3445`): for $Z \sim \mathcal{N}(0, 1)$,
the Mills ratio bound $\mathbb{P}(Z \ge t) \le \frac{e^{-t^2/2}}{t\sqrt{2\pi}}$ ($t > 0$),
the MGF formula $\mathbb{E}[e^{\theta Z}] = e^{\theta^2/2}$ ($\theta \in \mathbb{R}$), the
Proposition 7.1 bound $\mathbb{P}(Z \ge t) \le e^{\theta^2/2 - \theta t}$ ($\theta, t >
0$), optimality of the minimizer $\theta = t$ ($e^{-t^2/2} \le e^{\theta^2/2 - \theta t}$
for all $\theta \in \mathbb{R}$), and $\mathbb{P}(Z \ge t) \le e^{-t^2/2}$ ($t > 0$). -/
def Ex7_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → ℝ},
    AEMeasurable Z P →
    P.map Z = stdNormalLaw →
    (∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ Z ω} ≤ Real.exp (-t ^ 2 / 2) / (t * Real.sqrt (2 * Real.pi))) ∧
      (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * Z ω)) P ∧
        ∫ ω, Real.exp (θ * Z ω) ∂P = Real.exp (θ ^ 2 / 2)) ∧
      (∀ θ t : ℝ, 0 < θ → 0 < t →
        P.real {ω | t ≤ Z ω} ≤ Real.exp (θ ^ 2 / 2 - θ * t)) ∧
      (∀ θ t : ℝ, 0 < t → Real.exp (-t ^ 2 / 2) ≤ Real.exp (θ ^ 2 / 2 - θ * t)) ∧
      (∀ t : ℝ, 0 < t → P.real {ω | t ≤ Z ω} ≤ Real.exp (-t ^ 2 / 2))

/-- Example 7.2 (`\label{ex212}`, `SteinIntro.tex:3447-3461`; see `ISSUE-EX7.2` in
`docs/SOURCE-ISSUES.md` for the $e^{-t\log t}$ prose remark at `SteinIntro.tex:3458`): for
$Z \sim \mathrm{Po}(\lambda)$ with $\lambda > 0$, $\mathbb{E}[e^{\theta Z}] =
\exp(\lambda(e^\theta - 1))$ ($\theta \in \mathbb{R}$), $\mathbb{P}(Z - \lambda \ge t) \le
\exp(\lambda(e^\theta - 1) - \theta(t + \lambda))$ ($\theta, t > 0$), optimality of the
minimizer $\theta = \log(1 + t/\lambda)$ over all $\theta \in \mathbb{R}$, the resulting
tail bound $\mathbb{P}(Z - \lambda \ge t) \le B(\lambda, t)$, and $B(\lambda, t) = o(e^{-c
t})$ as $t \to \infty$ for every fixed $c > 0$. -/
def Ex7_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {Z : Ω → ℕ},
    0 < r →
    AEMeasurable Z P →
    P.map Z = poissonLaw r →
    let lam : ℝ := (r : ℝ)
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * (Z ω : ℝ))) P ∧
        ∫ ω, Real.exp (θ * (Z ω : ℝ)) ∂P = Real.exp (lam * (Real.exp θ - 1))) ∧
      (∀ θ t : ℝ, 0 < θ → 0 < t →
        P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤
          Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam))) ∧
      (∀ θ t : ℝ, 0 < t → B t ≤ Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam))) ∧
      (∀ t : ℝ, 0 < t → P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤ B t) ∧
      (∀ c : ℝ, 0 < c →
        Filter.Tendsto (fun t : ℝ ↦ B t / Real.exp (-c * t)) Filter.atTop (nhds 0))

/-- Example 7.2 lower-order prose comparison, corrected exponential-rate version
(`\label{ex212}`, `SteinIntro.tex:3458`, `SteinIntro.tex:3447`; `ISSUE-EX7.2` in
`docs/SOURCE-ISSUES.md`): for every $\lambda > 0$ and every $c > 1$, the Poisson Chernoff
bound $B(\lambda, t) = \exp(-t(\log(1 + t/\lambda) - 1) - \lambda\log(1 + t/\lambda))$
satisfies $\lim_{t \to \infty} e^{-c t \log t} / B(\lambda, t) = 0$.

Difference from printed result (`ISSUE-EX7.2`): relaxes the printed exponent $c = 1$ to $c > 1$
so the comparison holds for every $\lambda > 0$; the printed $c = 1$ claim fails whenever $0 <
\lambda \le e^{-1}$ (`poisson_bound_order_not_tendsto_of_le`). -/
def Ex7_2_order_corrected : Prop :=
  ∀ {lam c : ℝ},
    0 < lam →
    1 < c →
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    Filter.Tendsto (fun t : ℝ ↦ Real.exp (-c * t * Real.log t) / B t) Filter.atTop (nhds 0)

/-- Example 7.2 lower-order prose comparison, restricted to $\lambda > e^{-1}$
(`\label{ex212}`, `SteinIntro.tex:3458`, `SteinIntro.tex:3447`; `ISSUE-EX7.2` in
`docs/SOURCE-ISSUES.md`): for $\lambda > e^{-1}$, the Poisson Chernoff bound $B(\lambda, t)
= \exp(-t(\log(1 + t/\lambda) - 1) - \lambda\log(1 + t/\lambda))$ satisfies $\lim_{t \to
\infty} e^{-t\log t} / B(\lambda, t) = 0$.

Difference from printed result (`ISSUE-EX7.2`): restricts $\lambda > 0$ to $\lambda > e^{-1}$;
for $0 < \lambda \le e^{-1}$, $e^{-t\log t} / B(\lambda, t) \sim (e\lambda)^t (1 +
t/\lambda)^\lambda$ does not converge to $0$ (`poisson_bound_order_not_tendsto_of_le`). -/
def Ex7_2_order_restricted : Prop :=
  ∀ {lam : ℝ},
    Real.exp (-1) < lam →
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    Filter.Tendsto (fun t : ℝ ↦ Real.exp (-t * Real.log t) / B t) Filter.atTop (nhds 0)

/-- Section 7 prose MGF derivative identity (unlabeled prose, `SteinIntro.tex:3464-3469`): if
$\mathbb{E}[e^{\theta W}] < \infty$ for all $\theta \in (-\delta, \delta)$ ($\delta > 0$),
then $m(\theta) = \mathbb{E}[e^{\theta W}]$ satisfies $m'(\theta) = \mathbb{E}[W e^{\theta
W}]$ (and $W e^{\theta W}$ is integrable) for all $\theta \in (-\delta, \delta)$. -/
def Sec7_mgf_hasDerivAt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {δ : ℝ},
    AEMeasurable W P →
    0 < δ →
    (∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * W ω)) P) →
    ∀ θ ∈ Set.Ioo (-δ) δ,
      Integrable (fun ω ↦ W ω * Real.exp (θ * W ω)) P ∧
        HasDerivAt (fun u : ℝ ↦ ∫ ω, Real.exp (u * W ω) ∂P)
          (∫ ω, W ω * Real.exp (θ * W ω) ∂P) θ

/-- Theorem 7.2 (`\label{thm211a}`, eq. `(7.1)` `\label{122g}`, `SteinIntro.tex:3479-3489`):
concentration inequalities for an $a$-Stein pair $(W, W')$ with finite variance under the
linear conditional-variance bound $\mathbb{E}[(W' - W)^2 \mid \mathcal{F}] / (2a) \le B W +
C$, including the exact boundary vanishing at $C = 0$. -/
def Thm7_2 : Prop :=
  ∀ {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a B C : ℝ} {W W' : Ω → ℝ},
    IsSteinPair P a W W' →
    MemLp W 2 P →
    (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * W ω) * |W' ω - W ω|) P) →
    ∀ {m : MeasurableSpace Ω},
      MeasurableSpace.comap W inferInstance ≤ m →
      m ≤ m₀ →
      0 ≤ B →
      0 ≤ C →
      (∀ᵐ ω ∂P, P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a) ≤ B * W ω + C) →
      ∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ W ω} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
          P.real {ω | W ω ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * C)) ∧
          (C = 0 → P.real {ω | W ω ≤ -t} = 0) ∧
          (B = 0 → C = 0 → P.real {ω | t ≤ W ω} = 0)

/-- Remark 7.3 (unlabeled `remark`, `SteinIntro.tex:3490-3495`): condition `(7.1)`
($\mathbb{E}[(W' - W)^2 \mid \mathcal{F}] / (2a) \le B W + C$ with $a > 0$) implies $B W +
C \ge 0$ almost surely, hence $W \ge -C / B$ almost surely whenever $B > 0$. -/
def Rem7_3 : Prop :=
  ∀ {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω)
    {m : MeasurableSpace Ω} {a B C : ℝ} {W W' : Ω → ℝ},
    0 < a →
    m ≤ m₀ →
    (∀ᵐ ω ∂P, P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a) ≤ B * W ω + C) →
    (∀ᵐ ω ∂P, 0 ≤ B * W ω + C) ∧ (0 < B → ∀ᵐ ω ∂P, -C / B ≤ W ω)

/-- Example 7.4, Stein-pair setup (unlabeled `example`, `SteinIntro.tex:3497-3502`): for
independent square-integrable random variables $X_1, \dots, X_n$ with means $\mu_i =
\mathbb{E}[X_i]$, an independent copy $(X_1', \dots, X_n')$, and an independent uniform
index $I \in \{1, \dots, n\}$, $W = \sum_{i=1}^n (X_i - \mu_i)$ and $W' = W - X_I + X_I'$
form a $(1/n)$-Stein pair. -/
def Ex7_4_steinPair : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 2 P) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω - ∫ ω', X i ω' ∂P)
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    IsSteinPair P (1 / (n : ℝ)) W W'

/-- Example 7.4(1) (unlabeled `example` item 1, `SteinIntro.tex:3503-3515`): Hoeffding-type
concentration inequality $\mathbb{P}(|W - \mathbb{E}[W]| \ge t) \le 2 \exp\bigl(-t^2 /
\sum_{i=1}^n (\sigma_i^2 + C_i^2)\bigr)$ for $W = \sum_{i=1}^n (X_i - \mu_i)$ when $X_1,
\dots, X_n$ are independent with $|X_i - \mu_i| \le C_i$ a.s., including exact vanishing
when $\sum_i (\sigma_i^2 + C_i^2) = 0$. -/
def Ex7_4_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {C : Fin n → ℝ},
    0 < n →
    (∀ i : Fin n, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, 0 ≤ C i) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω - ∫ ω', X i ω' ∂P| ≤ C i) →
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω - ∫ ω', X i ω' ∂P)
    ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ |W ω - ∫ ω', W ω' ∂P|} ≤
        2 * Real.exp (-t ^ 2 / ∑ i : Fin n, (ProbabilityTheory.variance (X i) P + C i ^ 2)) ∧
      (∑ i : Fin n, (ProbabilityTheory.variance (X i) P + C i ^ 2) = 0 →
        P.real {ω | t ≤ |W ω - ∫ ω', W ω' ∂P|} = 0)

/-- Example 7.4(2), corrected (unlabeled `example` item 2, eq. `(7.2)` `\label{21198}`,
`SteinIntro.tex:3516-3536`; `ISSUE-EX7.4` in `docs/SOURCE-ISSUES.md`): for independent
random variables $X_1, \dots, X_n$ taking values in $[0, 1]$, with uncentered sum $S =
\sum_{i=1}^n X_i$ and $\mu = \mathbb{E}[S] = \sum_{i=1}^n \mathbb{E}[X_i]$, $\mathbb{P}(|S
- \mu| \ge t) \le 2 \exp(-t^2 / (2\mu + t))$ for all $t > 0$, and when $\sigma^2 =
\mathrm{Var}(S) > 0$, $\mathbb{P}(|S - \mu| / \sigma \ge t) \le 2 \exp(-t^2 / (2\mu /
\sigma^2 + t / \sigma))$.

Difference from printed result (`ISSUE-EX7.4`): resolves the notation overload between the
centered Stein-pair sum $W = \sum_{i=1}^n (X_i - \mu_i)$ of `SteinIntro.tex:3497-3502`
($\mathbb{E}[W] = 0$) and the uncentered sum $S = \sum_{i=1}^n X_i$ with $\mu = \mathbb{E}[S]$;
under a literal reading with $\mu = \mathbb{E}[W] = 0$, `(7.2)` reads $\mathbb{P}(|W| \ge t)
\le 2 e^{-t}$, which is false for $n = 16$ fair coins at $t = 2$. -/
def Ex7_4_2_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ},
    0 < n →
    (∀ i : Fin n, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ 1) →
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    (∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ |S ω - μ|} ≤ 2 * Real.exp (-t ^ 2 / (2 * μ + t))) ∧
      (0 < ProbabilityTheory.variance S P →
        ∀ t : ℝ, 0 < t →
          P.real {ω | t ≤ |S ω - μ| / σ} ≤
            2 * Real.exp (-t ^ 2 / (2 * (μ / σ ^ 2) + t / σ)))

/-- Example 7.4(2), exponential order of `(7.2)` (`\label{21198}`, `SteinIntro.tex:3528-3529`,
`SteinIntro.tex:3526`): for constant $\mu \ge 0$, $\exp(-t^2 / (2\mu + t)) / e^{-t} \to
e^{2\mu}$ as $t \to \infty$, so the upper bound `(7.2)` is of order $e^{-t}$. -/
def Ex7_4_2_order : Prop :=
  ∀ {μ : ℝ},
    0 ≤ μ →
    Filter.Tendsto
      (fun t : ℝ ↦ Real.exp (-t ^ 2 / (2 * μ + t)) / Real.exp (-t))
      Filter.atTop (nhds (Real.exp (2 * μ)))

/-- Section 7.1 display `(7.4)` (`\label{2212a}`, `SteinIntro.tex:3549-3552`, reused at
`SteinIntro.tex:3779` and `SteinIntro.tex:3831`): cleared-denominator exponential chord
inequality $|e^x - e^y| \le |x - y| \cdot (e^x + e^y) / 2$ for all $x, y \in \mathbb{R}$. -/
def Sec7_eq7_4 : Prop :=
  ∀ x y : ℝ,
    |Real.exp x - Real.exp y| ≤ |x - y| * (Real.exp x + Real.exp y) / 2

/-- Example 7.5, Stein-pair property restricted (unlabeled `example`,
`SteinIntro.tex:3597-3611`; `ISSUE-TYPO-7.5` and `ISSUE-7.5` in `docs/SOURCE-ISSUES.md`):
for an array $(a_{ij})_{1 \le i, j \le n}$ with $n \ge 2$, a uniform random permutation
$\sigma$ of `Fin n`, and an independent uniform transposition $\tau$, $W = \sum_i a_{i,
\sigma(i)} - \frac{1}{n}\sum_{i, j} a_{ij}$ and $W' = \sum_i a_{i, (\sigma\tau)(i)} -
\frac{1}{n}\sum_{i, j} a_{ij}$ satisfy $\mathbb{E}[W] = 0$, exchangeability of $(W, W')$,
$\mathbb{E}[W' \mid W] = (1 - \frac{2}{n - 1}) W$, and for $n \ge 3$ form a $\frac{2}{n -
1}$-Stein pair.

Difference from printed result (`ISSUE-TYPO-7.5`, `ISSUE-7.5`): corrects the centering typo
$\frac{1}{n^2}\sum_{i, j} a_{ij}$ to $\frac{1}{n}\sum_{i, j} a_{ij}$, restricts the
transposition construction to $n \ge 2$ (division by $n - 1$), and restricts Definition 3.2's
`a ≤ 1` clause (`IsSteinPair`) to $n \ge 3$ because $a = 2/(2 - 1) = 2 > 1$ at $n = 2$
(`not_combinatorial_isSteinPair_n2`). -/
def Ex7_5_steinPair_restricted : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → ℝ)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → {π : Equiv.Perm (Fin n) // π.IsSwap}},
    Measurable σ →
    Measurable τ →
    ProbabilityTheory.IndepFun σ τ P →
    P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure →
    P.map τ =
      (@PMF.uniformOfFintype {π : Equiv.Perm (Fin n) // π.IsSwap} inferInstance
        ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
          ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩).toMeasure →
    let W : Ω → ℝ :=
      fun ω ↦ (∑ i : Fin n, a i (σ ω i)) - (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    let W' : Ω → ℝ :=
      fun ω ↦
        (∑ i : Fin n, a i ((σ ω * (τ ω).1) i)) -
          (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    ∫ ω, W ω ∂P = 0 ∧
      IsExchangeablePair P W W' ∧
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        (fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω) ∧
      (3 ≤ n → IsSteinPair P (2 / ((n : ℝ) - 1)) W W')

/-- Proposition 7.3 (unlabeled `proposition` inside Example 7.5, `SteinIntro.tex:3612-3617`;
`ISSUE-TYPO-7.5` and `ISSUE-7.5` in `docs/SOURCE-ISSUES.md`): concentration inequality for
$W = \sum_{i=1}^n a_{i, \sigma(i)} - \frac{1}{n}\sum_{i, j} a_{ij}$ when $\sigma$ is a
uniform random permutation of `Fin n` and $0 \le a_{ij} \le 1$ (holding for all $n \in
\mathbb{N}$ via the general $a > 0$ library version of Theorem 7.2). -/
def Prop7_3 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {a : Fin n → Fin n → ℝ} {σ : Ω → Equiv.Perm (Fin n)},
    (∀ i j : Fin n, 0 ≤ a i j ∧ a i j ≤ 1) →
    AEMeasurable σ P →
    P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure →
    let W : Ω → ℝ :=
      fun ω ↦ (∑ i : Fin n, a i (σ ω i)) - (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ |W ω|} ≤
        2 * Real.exp (-t ^ 2 / ((4 / (n : ℝ)) * (∑ i : Fin n, ∑ j : Fin n, a i j) + 2 * t))

/-- Section 7.2 Curie–Weiss ground-state mode claim (unlabeled prose for `(7.6)`
(`\ref{2199}`), `SteinIntro.tex:3641`): for $\beta > 0$, the all-$(+1)$ spin configuration
uniquely maximizes the Curie–Weiss Gibbs weight and probability `(7.6)` when $h > 0$, the
all-$(-1)$ configuration uniquely maximizes `(7.6)` when $h < 0$, and at $h = 0$ both
constant configurations tie and strictly dominate every non-constant configuration. -/
def Sec7_curieWeiss_mode : Prop :=
  ∀ {n : ℕ} {β h : ℝ},
    0 < β →
    (0 < h →
        ∀ x : Fin n → Bool,
          x ≠ (fun _ ↦ true) →
          curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) ∧
            (curieWeissMeasure n β h).real {x} <
              (curieWeissMeasure n β h).real {fun _ ↦ true}) ∧
      (h < 0 →
        ∀ x : Fin n → Bool,
          x ≠ (fun _ ↦ false) →
          curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ false) ∧
            (curieWeissMeasure n β h).real {x} <
              (curieWeissMeasure n β h).real {fun _ ↦ false}) ∧
      (h = 0 →
        curieWeissWeight n β h (fun _ ↦ true) = curieWeissWeight n β h (fun _ ↦ false) ∧
          (curieWeissMeasure n β h).real {fun _ ↦ true} =
            (curieWeissMeasure n β h).real {fun _ ↦ false} ∧
          ∀ x : Fin n → Bool,
            x ≠ (fun _ ↦ true) →
            x ≠ (fun _ ↦ false) →
            curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) ∧
              (curieWeissMeasure n β h).real {x} <
                (curieWeissMeasure n β h).real {fun _ ↦ true})

/-- Proposition 7.4 (`\label{prop2112y}`, `SteinIntro.tex:3645-3653`): concentration of the
magnetization $m = \frac{1}{n}\sum_{i=1}^n \sigma_i$ around $\tanh(\beta m + \beta h)$
under the Curie–Weiss Gibbs measure `(7.6)` (`\ref{2199}`) for all $n \ge 1$, $\beta > 0$,
$h \in \mathbb{R}$, and $t \ge 0$. -/
def Prop7_4 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {β h t : ℝ} {X : Ω → Fin n → Bool},
    0 < n →
    0 < β →
    0 ≤ t →
    AEMeasurable X P →
    P.map X = curieWeissMeasure n β h →
    let m : Ω → ℝ := fun ω ↦ (∑ i : Fin n, spin (X ω i)) / (n : ℝ)
    P.real {ω | β / (n : ℝ) + t / Real.sqrt n ≤ |m ω - Real.tanh (β * m ω + β * h)|} ≤
      2 * Real.exp (-t ^ 2 / (4 * (1 + β)))

/-- Theorem 7.5 (`\label{thm211b}`, `SteinIntro.tex:3658-3676`): concentration inequalities for
$f(X) = \mathbb{E}[F(X, X') \mid X]$ where $(X, X')$ is an exchangeable pair on a Polish
space and $F$ is antisymmetric with $\frac{1}{2}\mathbb{E}[|(f(X) - f(X')) F(X, X')| \mid
X] \le B f(X) + C$, including exact vanishing at $C = 0$. -/
def Thm7_5 : Prop :=
  ∀ {Ω α : Type*} [MeasurableSpace Ω] [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X X' : Ω → α} {F : α × α → ℝ} {f : α → ℝ} {B C : ℝ},
    Measurable X →
    IsExchangeablePair P X X' →
    Measurable F →
    (∀ x x' : α, F (x, x') = -F (x', x)) →
    Measurable f →
    (fun ω ↦ f (X ω)) =ᵐ[P]
      P[fun ω ↦ F (X ω, X' ω) | MeasurableSpace.comap X inferInstance] →
    (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * f (X ω)) * |F (X ω, X' ω)|) P) →
    0 ≤ B →
    0 ≤ C →
    (∀ᵐ ω ∂P,
      (1 / 2 : ℝ) *
          P[fun ω' ↦ |(f (X ω') - f (X' ω')) * F (X ω', X' ω')| |
            MeasurableSpace.comap X inferInstance] ω ≤
        B * f (X ω) + C) →
    ∀ t : ℝ, 0 < t →
      P.real {ω | t < f (X ω)} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
        P.real {ω | f (X ω) ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * C)) ∧
        (C = 0 → P.real {ω | f (X ω) ≤ -t} = 0 ∧ P.real {ω | t < f (X ω)} = 0)

/-- Section 7.2 prose reduction from Theorem 7.5 to Theorem 7.2 (unlabeled prose,
`SteinIntro.tex:3677-3681`): for an $a$-Stein pair $(W, W')$, $F(w, w') = (w - w') / a$ is
antisymmetric, satisfies $\mathbb{E}[F(W, W') \mid W] = W$ a.s., and reduces Theorem 7.5's
quadratic-variation condition to `(7.1)` (`\ref{122g}`) with $\mathcal{F} = \sigma(W)$. -/
def Sec7_thm7_2_from_thm7_5 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ},
    IsSteinPair P a W W' →
    let F : ℝ × ℝ → ℝ := fun p ↦ (p.1 - p.2) / a
    (∀ w w' : ℝ, F (w, w') = -F (w', w)) ∧
      P[fun ω ↦ F (W ω, W' ω) | MeasurableSpace.comap W inferInstance] =ᵐ[P] W ∧
      (fun ω ↦
        (1 / 2 : ℝ) *
          P[fun ω' ↦ |(W ω' - W' ω') * F (W ω', W' ω')| |
            MeasurableSpace.comap W inferInstance] ω) =ᵐ[P]
        fun ω ↦
          P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
            MeasurableSpace.comap W inferInstance] ω / (2 * a)

/-- Theorem 7.6, corrected (`\label{thm211c}`, `SteinIntro.tex:3814-3826`; `ISSUE-7.6` in
`docs/SOURCE-ISSUES.md`): lower and upper tail concentration inequalities via a bounded
size-bias coupling $|X - X^s| \le C$ for $X \ge 0$ a.s. with $0 < \mathrm{Var}(X) < \infty$
and $t \ge 0$.

Difference from printed result (`ISSUE-7.6`): adds the omitted sign hypothesis $t \ge 0$; for
$t < 0$ the upper-tail denominator $C\mu/\sigma^2 + Ct/(2\sigma)$ vanishes at $t =
-2\mu/\sigma$ and becomes negative for $t < -2\mu/\sigma$, making the printed inequality false
(`not_sizeBias_tail_bounds_printed`). -/
def Thm7_6_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xs : Ω → ℝ} {C : ℝ},
    0 ≤ᵐ[P] X →
    MemLp X 2 P →
    0 < ProbabilityTheory.variance X P →
    IsSizeBias P X P Xs →
    (∀ᵐ ω ∂P, |X ω - Xs ω| ≤ C) →
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    ((X ≤ᵐ[P] Xs →
        ∀ t : ℝ, 0 ≤ t →
          P.real {ω | (X ω - μ) / σ ≤ -t} ≤
            Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2)))) ∧
      (Integrable (fun ω ↦ Real.exp ((2 / C) * X ω)) P →
        ∀ t : ℝ, 0 ≤ t →
          P.real {ω | t ≤ (X ω - μ) / σ} ≤
            Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t)))))

/-- Proof of Theorem 7.6(2), corrected optimization of `(7.12)` (`\label{2134b}`,
`SteinIntro.tex:3863-3870`; `ISSUE-7.6-PROOF` in `docs/SOURCE-ISSUES.md`): for $C, \mu,
\sigma, t > 0$ and $R(\theta) = \exp\bigl(\frac{\mu C \theta^2}{\sigma^2(2 -
C\theta/\sigma)} - \theta t\bigr)$ on $[0, 2\sigma/C)$, the printed choice
$\theta_{\mathrm{sub}} = t(C\mu/\sigma^2 + Ct/(2\sigma))^{-1}$ lies in $(0, 2\sigma/C)$ and
evaluates to Theorem 7.6(2)'s bound, while the true minimizer of $R$ on $[0, 2\sigma/C)$ is
$\theta_{\min} = \frac{2\sigma}{C}(1 - \sqrt{\mu/(\mu + \sigma t)}) <
\theta_{\mathrm{sub}}$ with $R(\theta_{\min}) < R(\theta_{\mathrm{sub}})$.

Difference from printed result (`ISSUE-7.6-PROOF`): replaces the proof's prose claim *"The
right hand side of this \eq{2134b} is minimized at"* (`SteinIntro.tex:3867`)
$\theta_{\mathrm{sub}}$ with the valid evaluation at $\theta_{\mathrm{sub}}$ together with the
exact minimizer $\theta_{\min}$ on $[0, 2\sigma/C)$ and strict inequality $R(\theta_{\min}) <
R(\theta_{\mathrm{sub}})$. -/
def Sec7_3_eq7_12_minimizer_corrected : Prop :=
  ∀ {C μ σ t : ℝ},
    0 < C →
    0 < μ →
    0 < σ →
    0 < t →
    let R : ℝ → ℝ := fun θ ↦
      Real.exp ((μ * C * θ ^ 2) / (σ ^ 2 * (2 - C * θ / σ)) - θ * t)
    let θ_sub : ℝ := t * (C * μ / σ ^ 2 + C * t / (2 * σ))⁻¹
    let θ_min : ℝ := (2 * σ / C) * (1 - Real.sqrt (μ / (μ + σ * t)))
    0 < θ_min ∧
      θ_min < θ_sub ∧
      θ_sub < 2 * σ / C ∧
      R θ_sub = Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t))) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ < 2 * σ / C → R θ_min ≤ R θ) ∧
      R θ_min < R θ_sub

/-- Example 7.6, corrected (unlabeled `example`, `SteinIntro.tex:3878-3884`; `ISSUE-EX7.6` and
`ISSUE-7.6` in `docs/SOURCE-ISSUES.md`): for i.i.d. $\mathrm{Bernoulli}(p)$ random
variables $Y_1, \dots, Y_n$ ($n \ge 1$, $k \ge 1$, $0 < p < 1$), cyclic $k$-runs $X_i =
\prod_{j=i}^{i+k-1} Y_j$, $X = \sum_{i=1}^n X_i$, and $X^s$ obtained by forcing the first
window's coins to $1$, $X^s$ is a monotone size-bias coupling of $X$ with $|X^s - X| \le 2k
- 1$ a.s., $\mu = \mathbb{E}[X] = n p^k$ when $n \ge k$, $\sigma^2 = \mathrm{Var}(X) =
\mu\bigl(1 - p^k + 2\sum_{r=1}^{k-1}(p^r - p^k)\bigr)$ when $n \ge 2k - 1$, and for all $t
\ge 0$, $\mathbb{P}(|(X - \mu)/\sigma| \ge t) \le 2 \exp\bigl(-t^2 / (2(2k - 1)(\mu /
\sigma^2 + t / (2\sigma)))\bigr)$.

Difference from printed result (`ISSUE-EX7.6`, `ISSUE-7.6`): restores the missing factor of $2$
on the off-diagonal covariance sum in $\sigma^2$ (`Ex7_6_variance_counterexample`), adds the
non-wrapping regime $n \ge 2k - 1$ for that variance formula (`n \ge k` for $\mu = n p^k$), and
includes $t \ge 0$ from `ISSUE-7.6`. -/
def Ex7_6_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n k : ℕ} (hn : 1 ≤ n) {p : ℝ} {Y : Fin n → Ω → ℝ},
    1 ≤ k →
    0 < p →
    p < 1 →
    (∀ i : Fin n, Measurable (Y i)) →
    ProbabilityTheory.iIndepFun Y P →
    (∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
    (∀ i : Fin n, P.real {ω | Y i ω = 1} = p) →
    let Yf : Fin n → Ω → ℝ := fun j ω ↦ if j.1 < k then 1 else Y j ω
    let X_run : (Fin n → Ω → ℝ) → Fin n → Ω → ℝ :=
      fun Z i ω ↦ ∏ r : Fin k, Z ⟨(i.1 + r.1) % n, Nat.mod_lt _ hn⟩ ω
    let X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_run Y i ω
    let Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_run Yf i ω
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    IsSizeBias P X P Xs ∧
      (X ≤ᵐ[P] Xs) ∧
      (∀ᵐ ω ∂P, |Xs ω - X ω| ≤ (2 * (k : ℝ) - 1)) ∧
      (k ≤ n → μ = (n : ℝ) * p ^ k) ∧
      (2 * k - 1 ≤ n →
        ProbabilityTheory.variance X P =
          μ * (1 - p ^ k + 2 * ∑ r ∈ Finset.Ico 1 k, (p ^ r - p ^ k))) ∧
      ∀ t : ℝ, 0 ≤ t →
        P.real {ω | t ≤ |(X ω - μ) / σ|} ≤
          2 * Real.exp (-t ^ 2 / (2 * (2 * (k : ℝ) - 1) * (μ / σ ^ 2 + t / (2 * σ))))

end SteinMethod
