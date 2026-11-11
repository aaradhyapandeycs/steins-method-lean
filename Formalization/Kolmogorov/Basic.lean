/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Kolmogorov
import Formalization.Defs.NormalStein
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Basic Properties & Non-Vacuity of `normalKolmogorovClass` (`Formalization.Kolmogorov.Basic`)

Establishes regularity, Lipschitz, local absolute continuity, and integrability properties for
functions in `normalKolmogorovClass` (Corollary 3.26, `\label{cor91}`, `SteinIntro.tex:1688-1694`),
together with concrete non-vacuity witnesses (`AGENTS.md` Rule 2 / Step 2).
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-! ### Section 1: Regularity and Integrability of `normalKolmogorovClass` -/

/-- Every $f \in \mathcal{F}$ (`normalKolmogorovClass`) is continuous
(Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem continuous_of_mem_normalKolmogorovClass {f : ℝ → ℝ}
    (hf : f ∈ normalKolmogorovClass) : Continuous f :=
  hf.1.continuous

/-- Every $f \in \mathcal{F}$ (`normalKolmogorovClass`) is $2$-Lipschitz
(Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem lipschitzWith_two_of_mem_normalKolmogorovClass {f : ℝ → ℝ}
    (hf : f ∈ normalKolmogorovClass) : LipschitzWith 2 f := by
  refine lipschitzWith_of_nnnorm_deriv_le hf.1 fun w ↦ ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
  exact hf.2.2.1 w

/-- Every $f \in \mathcal{F}$ (`normalKolmogorovClass`) is locally absolutely continuous on every
compact interval (Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`), allowing direct
application of `IsZeroBias` (Definition 3.10, ruling `D9`). -/
theorem absolutelyContinuousOnInterval_of_mem_normalKolmogorovClass {f : ℝ → ℝ}
    (hf : f ∈ normalKolmogorovClass) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b :=
  (lipschitzWith_two_of_mem_normalKolmogorovClass hf).lipschitzOnWith.absolutelyContinuousOnInterval

/-- For any finite measure $\mu$, a.e.-measurable $W$, and $f \in \mathcal{F}$, $f'(W)$ is
$\mu$-integrable (Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem integrable_deriv_comp_of_mem_normalKolmogorovClass
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {W : Ω → ℝ} {f : ℝ → ℝ} (hW : AEMeasurable W μ) (hf : f ∈ normalKolmogorovClass) :
    Integrable (fun ω ↦ deriv f (W ω)) μ := by
  refine Integrable.of_bound ((measurable_deriv f).comp_aemeasurable hW).aestronglyMeasurable 2 ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]
    exact hf.2.2.1 (W ω)

/-- For any measure $\mu$, $\mu$-integrable $W$, and $f \in \mathcal{F}$, $W f(W)$ is
$\mu$-integrable (Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem integrable_mul_comp_of_mem_normalKolmogorovClass
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {W : Ω → ℝ} {f : ℝ → ℝ} (hW : Integrable W μ) (hf : f ∈ normalKolmogorovClass) :
    Integrable (fun ω ↦ W ω * f (W ω)) μ := by
  have hfW : AEStronglyMeasurable (fun ω ↦ f (W ω)) μ :=
    (continuous_of_mem_normalKolmogorovClass hf).comp_aestronglyMeasurable hW.aestronglyMeasurable
  refine (hW.norm.mul_const (Real.sqrt (Real.pi / 2))).mono' (hW.aestronglyMeasurable.mul hfW) ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.2.1 (W ω)) (abs_nonneg (W ω))

/-- For any finite measure $\mu$, $\mu$-integrable $W$, and $f \in \mathcal{F}$,
$\mathcal{A}f(W) = f'(W) - W f(W)$ is $\mu$-integrable
(Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem integrable_normalSteinOp_of_mem_normalKolmogorovClass
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {W : Ω → ℝ} {f : ℝ → ℝ} (hW : Integrable W μ) (hf : f ∈ normalKolmogorovClass) :
    Integrable (fun ω ↦ normalSteinOp f (W ω)) μ :=
  (integrable_deriv_comp_of_mem_normalKolmogorovClass hW.aemeasurable hf).sub
    (integrable_mul_comp_of_mem_normalKolmogorovClass hW hf)

/-! ### Section 2: Non-Vacuity Witnesses (`AGENTS.md` Step 2) -/

/-- Non-vacuity (zero witness): the identically zero function belongs to `normalKolmogorovClass`
(Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem zero_mem_normalKolmogorovClass : (0 : ℝ → ℝ) ∈ normalKolmogorovClass := by
  refine ⟨differentiable_const 0, fun _ ↦ ?_, fun _ ↦ ?_, fun u v w ↦ ?_⟩
  · simp only [Pi.zero_apply, abs_zero]
    positivity
  · simp only [Pi.zero_def, deriv_const, abs_zero]
    norm_num
  · simp only [Pi.zero_apply, mul_zero, sub_self, abs_zero]
    positivity

private lemma hasDerivAt_gaussianBump (w : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (1 / 8 : ℝ) * Real.exp (-x ^ 2 / 2))
      (-(w / 8) * Real.exp (-w ^ 2 / 2)) w := by
  have h1 : HasDerivAt (fun x : ℝ ↦ -x ^ 2 / 2) (-w) w := by
    convert (hasDerivAt_pow 2 w).fun_neg.div_const (2 : ℝ) using 1
    ring
  convert (h1.exp.const_mul (1 / 8 : ℝ)) using 1
  ring

private lemma abs_mul_exp_neg_sq_div_two_le (w : ℝ) :
    |w| * Real.exp (-w ^ 2 / 2) ≤ 1 := by
  have hexp : w ^ 2 / 2 + 1 ≤ Real.exp (w ^ 2 / 2) := Real.add_one_le_exp (w ^ 2 / 2)
  have habs : |w| ≤ w ^ 2 / 2 + 1 := by
    nlinarith [sq_nonneg (|w| - 1), sq_abs w]
  have hneg : -w ^ 2 / 2 = -(w ^ 2 / 2) := by ring
  rw [hneg, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact habs.trans hexp

/-- Concrete nontrivial witness: the Gaussian bump $f(w) = \frac{1}{8} e^{-w^2/2}$ belongs to
`normalKolmogorovClass` (Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem gaussianBump_mem_normalKolmogorovClass :
    (fun w : ℝ ↦ (1 / 8 : ℝ) * Real.exp (-w ^ 2 / 2)) ∈ normalKolmogorovClass := by
  set f : ℝ → ℝ := fun w ↦ (1 / 8 : ℝ) * Real.exp (-w ^ 2 / 2)
  have hf_deriv : ∀ w : ℝ, HasDerivAt f (-(w / 8) * Real.exp (-w ^ 2 / 2)) w :=
    hasDerivAt_gaussianBump
  refine ⟨fun w ↦ (hf_deriv w).differentiableAt, fun w ↦ ?_, fun w ↦ ?_, fun u v w ↦ ?_⟩
  · have hexp_le : Real.exp (-w ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg w])
    have hpi : (1 / 8 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
    rw [abs_of_pos (by positivity)]
    exact (mul_le_of_le_one_right (by norm_num) hexp_le).trans hpi
  · rw [(hf_deriv w).deriv, abs_mul, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8),
      abs_of_pos (Real.exp_pos _), div_mul_eq_mul_div]
    linarith [abs_mul_exp_neg_sq_div_two_le w]
  · set g : ℝ → ℝ := fun x ↦ x * f x
    have hg_deriv : ∀ x : ℝ, HasDerivAt g ((1 / 8 : ℝ) * (1 - x ^ 2) * Real.exp (-x ^ 2 / 2)) x :=
      fun x ↦ by
        have hmul := (hasDerivAt_id' x).mul (hf_deriv x)
        refine hmul.congr_deriv ?_
        dsimp only [f]
        ring
    have hg_lip : LipschitzWith (1 / 4 : ℝ≥0) g := by
      refine lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hg_deriv x).differentiableAt) fun x ↦ ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, (hg_deriv x).deriv]
      have hquad : |1 - x ^ 2| * Real.exp (-x ^ 2 / 2) ≤ 2 := by
        have h1 : |1 - x ^ 2| ≤ 2 * (x ^ 2 / 2 + 1) := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg x]
        have h2 : x ^ 2 / 2 + 1 ≤ Real.exp (x ^ 2 / 2) := Real.add_one_le_exp (x ^ 2 / 2)
        have hneg : -x ^ 2 / 2 = -(x ^ 2 / 2) := by ring
        rw [hneg, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
        linarith
      push_cast
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8),
        abs_of_pos (Real.exp_pos _), mul_assoc]
      linarith
    have hdist := hg_lip.dist_le_mul (w + u) (w + v)
    rw [Real.dist_eq, Real.dist_eq, show ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 by push_cast; ring] at hdist
    have huv : |(w + u) - (w + v)| ≤ |u| + |v| := by
      rw [show (w + u) - (w + v) = u - v by ring]
      exact abs_sub u v
    have hquarter : (1 / 4 : ℝ) ≤ |w| + Real.sqrt (2 * Real.pi) / 4 := by
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
      linarith [abs_nonneg w]
    calc
      |g (w + u) - g (w + v)| ≤ (1 / 4 : ℝ) * (|u| + |v|) :=
        hdist.trans (mul_le_mul_of_nonneg_left huv (by norm_num))
      _ ≤ (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|) :=
        mul_le_mul_of_nonneg_right hquarter (by positivity)

/-- Non-vacuity (nontrivial witness): `normalKolmogorovClass` contains a nonzero function
(Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem exists_ne_zero_mem_normalKolmogorovClass :
    ∃ f ∈ normalKolmogorovClass, f ≠ 0 := by
  refine ⟨fun w ↦ (1 / 8 : ℝ) * Real.exp (-w ^ 2 / 2), gaussianBump_mem_normalKolmogorovClass,
    fun h ↦ ?_⟩
  have h0 := congr_fun h 0
  simp only [ neg_zero, zero_pow (two_ne_zero), zero_div, Real.exp_zero, mul_one,
    Pi.zero_apply] at h0
  norm_num at h0

end SteinMethod
