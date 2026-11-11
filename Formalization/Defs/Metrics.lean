/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Integral Probability Metrics (`Formalization.Defs.Metrics`)

`ℝ≥0∞`-valued integral probability metrics (Kolmogorov, Wasserstein-1, and total variation) per
rulings `D1`–`D3` of `docs/AUTHOR_RULINGS.md` (`RULING-USER-2026-11-11`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- General integral probability metric $d_{\mathcal{H}}(\mu, \nu)$ valued in `ℝ≥0∞` over
integrable test functions in `H` (eq. `(1.1)` `\label{23}`, `SteinIntro.tex:503-509`;
eq. `(2.4)` `\label{32}`, `SteinIntro.tex:655-659`; ruling `D1`). -/
noncomputable def ipm {α : Type*} [MeasurableSpace α]
    (H : Set (α → ℝ)) (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ h ∈ H, ⨆ (_ : Integrable h μ ∧ Integrable h ν),
    ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)|

/-- Kolmogorov metric $d_{\mathrm{K}}(\mu, \nu)$ induced by half-line indicators
$\{\mathbb{I}[\cdot \le x] : x \in \mathbb{R}\}$
(Section 1.1.1 item 1 `\label{probmet}`, `SteinIntro.tex:513-515`; rulings `D1`–`D2`). -/
noncomputable def kolmogorovDist (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ipm {h : ℝ → ℝ | ∃ x : ℝ, h = (Set.Iic x).indicator 1} μ ν

/-- Wasserstein-1 metric $d_{\mathrm{W}}(\mu, \nu)$ induced by $1$-Lipschitz functions on `ℝ`
(Section 1.1.1 item 2 `\label{probmet}`, `SteinIntro.tex:516-519`; rulings `D1`–`D2`). -/
noncomputable def wassersteinDist (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ipm {h : ℝ → ℝ | LipschitzWith 1 h} μ ν

/-- Total variation metric $d_{\mathrm{TV}}(\mu, \nu)$ on any measurable space `α`, induced by
measurable set indicators $\{\mathbb{I}[\cdot \in A] : A \text{ measurable}\}$
(Section 1.1.1 item 3 `\label{probmet}`, `SteinIntro.tex:520-521`; Proposition 1.2(3)
`\label{prop22}`, `SteinIntro.tex:532-535`; rulings `D1`–`D3`). -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  ipm {h : α → ℝ | ∃ A : Set α, MeasurableSet A ∧ h = A.indicator 1} μ ν

end SteinMethod
