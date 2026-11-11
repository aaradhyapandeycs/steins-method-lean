/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Couplings
import Formalization.Defs.Laws
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Zero-Bias Density and Convergence Imports (`Formalization.Defs.ZeroBias`)

Canonical Lebesgue density `zeroBiasDensity` of the zero-bias distribution from Section 3.5
(Proposition 3.19(2) `\label{i82}`, eq. `(3.32)` `\label{82}`, `SteinIntro.tex:1479-1484`), together
with Mathlib's convergence-in-measure (`TendstoInMeasure`) and weak-convergence
(`ProbabilityMeasure`) imports used in Section 3.5.2 (`SteinIntro.tex:1554-1648`).
-/

open MeasureTheory

namespace SteinMethod

/-- Canonical Lebesgue density $p^z(w) = \sigma^{-2}\,\mathbb{E}[W \mathbf{1}_{W > w}]$ of the
zero-bias distribution with respect to $W$ (Proposition 3.19(2) `\label{i82}`, eq. `(3.32)`
`\label{82}`, `SteinIntro.tex:1479-1484`; `ISSUE-3.19`). -/
noncomputable def zeroBiasDensity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : Ω → ℝ) (w : ℝ) : ℝ :=
  (ProbabilityTheory.variance W P)⁻¹ * ∫ ω, W ω * (Set.Ioi w).indicator 1 (W ω) ∂P

end SteinMethod
