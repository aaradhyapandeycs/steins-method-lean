/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UnitInterval

/-!
# Exponential Stein Objects & Equilibrium Coupling (`Formalization.Defs.Exponential`)

Core definitions for Section 5 of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`, `SteinIntro.tex:2712-2984`): exponential distributions (`expLaw`,
`stdExpLaw`), expectation `stdExpExpect`, the exponential Stein characterizing operator
`expSteinOp`, Stein equation solutions `expSteinSol`, smooth Wasserstein/Kolmogorov test classes
(`expWassersteinClass`, `expKolmogorovClass`), the equilibrium distributional relation
`IsEquilibrium`, and the positive-support geometric distribution `shiftedGeomLaw`.
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-- Exponential distribution $\mathrm{Exp}(\lambda)$ on $\mathbb{R}$ with density
$\lambda e^{-\lambda z}$ on $(0, \infty)$ for $\lambda > 0$
(Definition 5.1, `SteinIntro.tex:2721-2724`), reusing `ProbabilityTheory.expMeasure`. -/
noncomputable abbrev expLaw (r : ℝ) : Measure ℝ :=
  ProbabilityTheory.expMeasure r

/-- Standard rate-$1$ exponential distribution $\mathrm{Exp}(1)$ on $\mathbb{R}$
(Definition 5.1, `SteinIntro.tex:2721-2724`). -/
noncomputable abbrev stdExpLaw : Measure ℝ :=
  ProbabilityTheory.expMeasure 1

/-- Expectation $\mathbb{E}[h(Z)]$ with respect to $Z \sim \mathrm{Exp}(1)$
(Lemma 5.2 `\label{lem172}`, eq. `(5.1)` `\label{171}`, `SteinIntro.tex:2741-2745`). -/
noncomputable def stdExpExpect (h : ℝ → ℝ) : ℝ :=
  ∫ x, h x ∂stdExpLaw

/-- Standard exponential Stein characterizing operator
$\mathcal{A}f(x) = f'(x) - f(x) + f(0)$
(Lemma 5.1 `\label{lem171}`, `SteinIntro.tex:2726-2730`). -/
noncomputable def expSteinOp (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x - f x + f 0

/-- Canonical solution $f_h(x) = -e^x \int_x^\infty (h(t) - \mathbb{E}[h(Z)]) e^{-t}\,dt$
of the exponential Stein equation $f_h'(x) - f_h(x) = h(x) - \mathbb{E}[h(Z)]$ with $f_h(0) = 0$
(Lemma 5.2 `\label{lem172}`, eq. `(5.2)` `\label{172}`, `SteinIntro.tex:2740-2745, 2775-2779`). -/
noncomputable def expSteinSol (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  -Real.exp x * ∫ t in Set.Ioi x, (h t - stdExpExpect h) * Real.exp (-t)

/-- Smooth test-function class
$\mathcal{F}_W = \{f : \|f'\| \le 1,\ \|f''\| \le 2,\ f(0) = 0\}$ for Wasserstein exponential
approximation (Theorem 5.3(1) `\label{thm171}`, `SteinIntro.tex:2761-2766`; ruling `D6`). -/
def expWassersteinClass : Set (ℝ → ℝ) :=
  {f | Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧
    (∀ x, |deriv f x| ≤ 1) ∧ (∀ x, |deriv (deriv f) x| ≤ 2) ∧ f 0 = 0}

/-- Differentiable test-function class
$\mathcal{F}_K = \{f : \|f\| \le 1,\ \|f'\| \le 2,\ f(0) = 0\}$ for Kolmogorov exponential
approximation (Theorem 5.3(2) `\label{thm171}`, `SteinIntro.tex:2767-2771`; ruling `D6`). -/
def expKolmogorovClass : Set (ℝ → ℝ) :=
  {f | Differentiable ℝ f ∧ (∀ x, |f x| ≤ 1) ∧ (∀ x, |deriv f x| ≤ 2) ∧ f 0 = 0}

/-- Equilibrium distributional relation $\mathbb{E}[f(W)] - f(0) = \mu\,\mathbb{E}[f'(W^e)]$
for all Lipschitz $f : \mathbb{R} \to \mathbb{R}$, where $W \ge 0$ a.s. has finite mean
$\mu = \mathbb{E}[W]$
(Definition 5.2, eq. `(5.3)` `\label{173}`, `SteinIntro.tex:2836-2843`). -/
def IsEquilibrium {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (W : Ω → ℝ) (P' : Measure Ω') (We : Ω' → ℝ) : Prop :=
  (0 ≤ᵐ[P] W) ∧ Integrable W P ∧ AEMeasurable We P' ∧
    ∀ f : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K f) →
      (∫ ω, f (W ω) ∂P) - f 0 = (∫ ω, W ω ∂P) * ∫ ω', deriv f (We ω') ∂P'

/-- Positive-support geometric distribution $\mathrm{Ge}(p)$ on $\{1, 2, \dots\} \subset \mathbb{N}$
with point probabilities $\mathbb{P}(N = k) = (1 - p)^{k - 1} p$ for $k \ge 1$ and $0 < p \le 1$
(Example 5.4 `\label{ex171}`, `SteinIntro.tex:2884`), reusing `ProbabilityTheory.geometricMeasure`
via `Set.projIcc 0 1 zero_le_one p` and shifted by `+ 1`. -/
noncomputable def shiftedGeomLaw (p : ℝ) : Measure ℕ :=
  (ProbabilityTheory.geometricMeasure (Set.projIcc 0 1 zero_le_one p)).map (· + 1)

end SteinMethod
