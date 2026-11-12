/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Basic

/-!
# Ornstein–Uhlenbeck Transition Kernel (`Formalization.Defs.OrnsteinUhlenbeck`)

Transition kernel of the stationary Ornstein–Uhlenbeck diffusion $(D(t))_{t \ge 0}$ for Remark 3.5
(`SteinIntro.tex:1009-1024`).
-/

open MeasureTheory

namespace SteinMethod

/-- Transition kernel of the Ornstein–Uhlenbeck diffusion over time increment `a`
(Remark 3.5, `SteinIntro.tex:1009-1024`): for `0 < a`, maps `x : ℝ` to the Gaussian law
`𝒩(e^{-a} x, 1 - e^{-2a})`; for `a ≤ 0`, defaults to `ProbabilityTheory.Kernel.id`
(`x ↦ Measure.dirac x`) as a totality convention. -/
noncomputable def ouKernel (a : ℝ) : ProbabilityTheory.Kernel ℝ ℝ :=
  if 0 < a then
    { toFun := fun x ↦
        ProbabilityTheory.gaussianReal (Real.exp (-a) * x)
          (Real.toNNReal (1 - Real.exp (-2 * a)))
      measurable' := ProbabilityTheory.measurable_gaussianReal.comp
        ((measurable_const.mul measurable_id).prodMk measurable_const) }
  else
    ProbabilityTheory.Kernel.id

end SteinMethod
