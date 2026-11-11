/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Target Probability Laws (`Formalization.Defs.Laws`)

Normal and Poisson probability distributions for Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`, `SteinIntro.tex`), reusing Mathlib's Gaussian and Poisson measures.
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-- Normal distribution $\mathcal{N}(\mu, v)$ on $\mathbb{R}$ with mean `μ` and variance `v ≥ 0`
(Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:562-574`, `630-635`). -/
noncomputable abbrev normalLaw (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  ProbabilityTheory.gaussianReal μ v

/-- Standard normal distribution $\mathcal{N}(0, 1)$ on $\mathbb{R}$
(Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:562-574`). -/
noncomputable abbrev stdNormalLaw : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 1

/-- Standard normal probability density $\phi(x) = (2\pi)^{-1/2} e^{-x^2/2}$
(proof of Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
noncomputable abbrev stdNormalPDF (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x

/-- Standard normal cumulative distribution function $\Phi(x) = \mathbb{P}(Z \le x)$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:353`; Lemma 2.2 `\label{lem2}`,
`SteinIntro.tex:578-588`). -/
noncomputable abbrev stdNormalCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf stdNormalLaw x

/-- Poisson distribution $\mathrm{Po}(r)$ on $\mathbb{N}$ with parameter `r : ℝ≥0`
(Lemma 4.1 `\label{lem101}` and Lemma 4.2 `\label{lem102}`, `SteinIntro.tex:1823-1848`). -/
noncomputable abbrev poissonLaw (r : ℝ≥0) : Measure ℕ :=
  ProbabilityTheory.poissonMeasure r

end SteinMethod
