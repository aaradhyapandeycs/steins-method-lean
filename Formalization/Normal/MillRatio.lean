/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.NormalStein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Standard Normal Calculus, Mill's Ratio, and Stein Kernels (`Formalization.Normal.MillRatio`)

Real analysis, Gaussian expectation bridges, Mill's ratio tail bounds, and the sharp
Chen–Goldstein–Shao (2011) Lemma 2.4 Green's kernel inequality for Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex`, Lemma 2.1 `\label{lem1}`,
Lemma 2.2 `\label{lem2}`, and Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:562-694`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace SteinMethod

/-! ### Section 1: Standard Normal Expectation, PDF, and CDF Calculus -/

/-- Expectation of $\mathbb{I}[\cdot \le x]$ under $\mathcal{N}(0,1)$ equals $\Phi(x)$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`; Section 2, `SteinIntro.tex:663`). -/
theorem stdNormalExpect_indicator_Iic (x : ℝ) :
    stdNormalExpect ((Set.Iic x).indicator 1) = stdNormalCDF x := by
  rw [stdNormalExpect, integral_indicator_one measurableSet_Iic, stdNormalCDF, cdf_eq_real,
    stdNormalLaw]

/-- Integrability under `stdNormalLaw` iff Lebesgue-integrable against `stdNormalPDF`
(Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:562-574`, `630-635`). -/
theorem integrable_stdNormalLaw_iff {h : ℝ → ℝ} :
    Integrable h stdNormalLaw ↔ Integrable (fun t ↦ stdNormalPDF t * h t) volume := by
  rw [stdNormalLaw, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  exact integrable_congr (ae_of_all _ fun t ↦ by dsimp only; rw [toReal_gaussianPDF, smul_eq_mul])

/-- Standard normal expectation as a Lebesgue integral against `stdNormalPDF`
(Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`; Section 2, `SteinIntro.tex:663`). -/
theorem stdNormalExpect_eq_integral_mul_pdf (h : ℝ → ℝ) :
    stdNormalExpect h = ∫ t, stdNormalPDF t * h t := by
  rw [stdNormalExpect, integral_gaussianReal_eq_integral_smul one_ne_zero]
  exact integral_congr_ae (ae_of_all _ fun t ↦ smul_eq_mul (stdNormalPDF t) (h t))

/-- Explicit formula for $\phi(w)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem stdNormalPDF_eq (w : ℝ) :
    stdNormalPDF w = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
  simp [stdNormalPDF, gaussianPDFReal]

/-- Value $\phi(0) = (\sqrt{2\pi})^{-1}$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem stdNormalPDF_zero : stdNormalPDF 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by
  simp [stdNormalPDF_eq]

/-- Positivity $0 < \phi(w)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem stdNormalPDF_pos (w : ℝ) : 0 < stdNormalPDF w := gaussianPDFReal_pos 0 1 w one_ne_zero

/-- Nonnegativity $0 \le \phi(w)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem stdNormalPDF_nonneg (w : ℝ) : 0 ≤ stdNormalPDF w := (stdNormalPDF_pos w).le

/-- Evenness $\phi(-w) = \phi(w)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem stdNormalPDF_even (w : ℝ) : stdNormalPDF (-w) = stdNormalPDF w := by simp [stdNormalPDF_eq]

/-- Global maximum $\phi(w) \le \phi(0)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem stdNormalPDF_le_zero (w : ℝ) : stdNormalPDF w ≤ stdNormalPDF 0 := by
  rw [stdNormalPDF_eq, stdNormalPDF_zero]
  have hexp : Real.exp (-w ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg w])
  simpa using mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Continuity of `stdNormalPDF` (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
@[fun_prop]
theorem continuous_stdNormalPDF : Continuous stdNormalPDF := by
  have h : stdNormalPDF = fun w ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
    ext w; exact stdNormalPDF_eq w
  rw [h]; fun_prop

/-- Integrability of `stdNormalPDF` (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
@[fun_prop]
theorem integrable_stdNormalPDF : Integrable stdNormalPDF := integrable_gaussianPDFReal 0 1

/-- Derivative $\phi'(w) = -w \phi(w)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem hasDerivAt_stdNormalPDF (w : ℝ) :
    HasDerivAt stdNormalPDF (-w * stdNormalPDF w) w := by
  have hfn : stdNormalPDF = fun t ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
    ext t; exact stdNormalPDF_eq t
  have hquad : HasDerivAt (fun t : ℝ ↦ -t ^ 2 / 2) (-w) w := by
    convert (((hasDerivAt_pow 2 w).neg).div_const 2) using 1; ring
  have hexp : HasDerivAt (fun t ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2))
      (-w * stdNormalPDF w) w := by
    convert (hquad.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹) using 1
    rw [stdNormalPDF_eq]; ring
  rwa [← hfn] at hexp

/-- Differentiability of `stdNormalPDF` (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
@[fun_prop]
theorem differentiable_stdNormalPDF : Differentiable ℝ stdNormalPDF :=
  fun w ↦ (hasDerivAt_stdNormalPDF w).differentiableAt

/-- Formula for `deriv stdNormalPDF w` (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem deriv_stdNormalPDF (w : ℝ) : deriv stdNormalPDF w = -w * stdNormalPDF w :=
  (hasDerivAt_stdNormalPDF w).deriv

/-- Normalization $\int \phi = 1$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem integral_stdNormalPDF : ∫ t, stdNormalPDF t = 1 :=
  integral_gaussianPDFReal_eq_one 0 one_ne_zero

private theorem exp_neg_sq_div_two_eq :
    (fun t : ℝ ↦ Real.exp (-t ^ 2 / 2)) = fun t ↦ Real.sqrt (2 * Real.pi) * stdNormalPDF t := by
  ext t; rw [stdNormalPDF_eq, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- Integrability of $e^{-t^2/2}$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem integrable_exp_neg_sq_div_two : Integrable (fun t : ℝ ↦ Real.exp (-t ^ 2 / 2)) := by
  rw [exp_neg_sq_div_two_eq]; exact integrable_stdNormalPDF.const_mul _

/-- Gaussian integral of $e^{-t^2/2}$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem integral_exp_neg_sq_div_two : ∫ t, Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  rw [exp_neg_sq_div_two_eq, integral_const_mul, integral_stdNormalPDF, mul_one]

/-- Integral form of $\Phi(w)$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_eq_integral_Iic (w : ℝ) :
    stdNormalCDF w = ∫ t in Iic w, stdNormalPDF t := by
  have hcdf : ENNReal.ofReal (stdNormalCDF w) =
      ENNReal.ofReal (∫ t in Iic w, stdNormalPDF t) := by
    rw [stdNormalCDF, stdNormalLaw, ofReal_cdf,
      gaussianReal_apply_eq_integral 0 one_ne_zero (Iic w)]
  exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ w)
    (integral_nonneg fun t ↦ stdNormalPDF_nonneg t)).mp hcdf

/-- Tail integral form of $1 - \Phi(w)$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem one_sub_stdNormalCDF_eq_integral_Ioi (w : ℝ) :
    1 - stdNormalCDF w = ∫ t in Ioi w, stdNormalPDF t := by
  have huniv : (∫ t in Iic w, stdNormalPDF t) + ∫ t in Ioi w, stdNormalPDF t = 1 := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      integrable_stdNormalPDF.integrableOn integrable_stdNormalPDF.integrableOn,
      Iic_union_Ioi, setIntegral_univ, integral_stdNormalPDF]
  rw [stdNormalCDF_eq_integral_Iic]; linarith

/-- Right-tail Gaussian integral $\int_{(w, \infty)} e^{-t^2/2}\,dt = \sqrt{2\pi}(1 - \Phi(w))$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:584-587`, `620-622`). -/
theorem integral_Ioi_exp_neg_sq_div_two (w : ℝ) :
    ∫ t in Ioi w, Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * Real.pi) * (1 - stdNormalCDF w) := by
  rw [exp_neg_sq_div_two_eq, integral_const_mul, one_sub_stdNormalCDF_eq_integral_Ioi]

/-- Left-tail Gaussian integral $\int_{(-\infty, w]} e^{-t^2/2}\,dt = \sqrt{2\pi}\Phi(w)$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:584-587`, `620-622`). -/
theorem integral_Iic_exp_neg_sq_div_two (w : ℝ) :
    ∫ t in Iic w, Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * Real.pi) * stdNormalCDF w := by
  rw [exp_neg_sq_div_two_eq, integral_const_mul, stdNormalCDF_eq_integral_Iic]

/-- Symmetry $\Phi(-w) = 1 - \Phi(w)$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_neg (w : ℝ) : stdNormalCDF (-w) = 1 - stdNormalCDF w := by
  rw [one_sub_stdNormalCDF_eq_integral_Ioi, stdNormalCDF_eq_integral_Iic]
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding stdNormalPDF (Ioi w)
  have hpre : (Neg.neg ⁻¹' Ioi w) = Iio (-w) := by ext t; simp
  rw [← hneg, hpre, setIntegral_congr_set Iio_ae_eq_Iic]
  exact setIntegral_congr_fun measurableSet_Iic fun t _ ↦ (stdNormalPDF_even t).symm

/-- Value $\Phi(0) = 1 / 2$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_zero : stdNormalCDF 0 = 1 / 2 := by
  have h := stdNormalCDF_neg 0; rw [neg_zero] at h; linarith

/-- Nonnegativity $0 \le \Phi(w)$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_nonneg (w : ℝ) : 0 ≤ stdNormalCDF w := cdf_nonneg _ w

/-- Upper bound $\Phi(w) \le 1$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_le_one (w : ℝ) : stdNormalCDF w ≤ 1 := cdf_le_one _ w

/-- Limit $\Phi(-\infty) = 0$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem tendsto_stdNormalCDF_atBot : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _

/-- Limit $\Phi(+\infty) = 1$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem tendsto_stdNormalCDF_atTop : Tendsto stdNormalCDF atTop (𝓝 1) := tendsto_cdf_atTop _

private theorem stdNormalCDF_eq_add_intervalIntegral (x : ℝ) :
    stdNormalCDF x = stdNormalCDF 0 + ∫ t in (0 : ℝ)..x, stdNormalPDF t := by
  simp_rw [stdNormalCDF_eq_integral_Iic]
  rcases le_total 0 x with hx | hx
  · have hunion : Iic 0 ∪ Ioc 0 x = Iic x := Iic_union_Ioc_eq_Iic hx
    have hdisj : Disjoint (Iic (0 : ℝ)) (Ioc 0 x) :=
      disjoint_left.mpr fun t ht1 ht2 ↦ not_lt_of_ge ht1 ht2.1
    rw [intervalIntegral.integral_of_le hx, ← setIntegral_union hdisj measurableSet_Ioc
      integrable_stdNormalPDF.integrableOn integrable_stdNormalPDF.integrableOn, hunion]
  · have hunion : Iic x ∪ Ioc x 0 = Iic (0 : ℝ) := Iic_union_Ioc_eq_Iic hx
    have hdisj : Disjoint (Iic x) (Ioc x 0) :=
      disjoint_left.mpr fun t ht1 ht2 ↦ not_lt_of_ge ht1 ht2.1
    have hsum : (∫ t in Iic x, stdNormalPDF t) + ∫ t in Ioc x 0, stdNormalPDF t =
        ∫ t in Iic (0 : ℝ), stdNormalPDF t := by
      rw [← setIntegral_union hdisj measurableSet_Ioc
        integrable_stdNormalPDF.integrableOn integrable_stdNormalPDF.integrableOn, hunion]
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hx]; linarith

/-- Derivative $\Phi'(w) = \phi(w)$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem hasDerivAt_stdNormalCDF (w : ℝ) :
    HasDerivAt stdNormalCDF (stdNormalPDF w) w := by
  have hfn : stdNormalCDF = fun x ↦ stdNormalCDF 0 + ∫ t in (0 : ℝ)..x, stdNormalPDF t := by
    ext x; exact stdNormalCDF_eq_add_intervalIntegral x
  rw [hfn]
  simpa using (intervalIntegral.integral_hasDerivAt_right
    (continuous_stdNormalPDF.intervalIntegrable 0 w)
    (continuous_stdNormalPDF.stronglyMeasurableAtFilter volume (𝓝 w))
    continuous_stdNormalPDF.continuousAt).const_add (stdNormalCDF 0)

/-- Differentiability of `stdNormalCDF` (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
@[fun_prop]
theorem differentiable_stdNormalCDF : Differentiable ℝ stdNormalCDF :=
  fun w ↦ (hasDerivAt_stdNormalCDF w).differentiableAt

/-- Formula `deriv stdNormalCDF w = stdNormalPDF w` (Lemma 2.2 `\label{lem2}`,
`SteinIntro.tex:578-588`). -/
theorem deriv_stdNormalCDF (w : ℝ) : deriv stdNormalCDF w = stdNormalPDF w :=
  (hasDerivAt_stdNormalCDF w).deriv

/-- Continuity of `stdNormalCDF` (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
@[fun_prop]
theorem continuous_stdNormalCDF : Continuous stdNormalCDF := differentiable_stdNormalCDF.continuous

/-- Strict monotonicity of `stdNormalCDF` (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem strictMono_stdNormalCDF : StrictMono stdNormalCDF :=
  strictMono_of_deriv_pos fun w ↦ by
    rw [(hasDerivAt_stdNormalCDF w).deriv]; exact stdNormalPDF_pos w

/-- Strict positivity $0 < \Phi(w)$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_pos (w : ℝ) : 0 < stdNormalCDF w :=
  lt_of_le_of_lt (cdf_nonneg _ (w - 1)) (strictMono_stdNormalCDF (by linarith))

/-- Strict upper bound $\Phi(w) < 1$ (Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem stdNormalCDF_lt_one (w : ℝ) : stdNormalCDF w < 1 :=
  lt_of_lt_of_le (strictMono_stdNormalCDF (by linarith : w < w + 1)) (cdf_le_one _ (w + 1))

private theorem tendsto_rpow_abs_mul_stdNormalPDF_cocompact (s : ℝ) :
    Tendsto (fun w : ℝ ↦ |w| ^ s * stdNormalPDF w) (cocompact ℝ) (𝓝 0) := by
  have hatTop : Tendsto (fun y : ℝ ↦ y ^ s * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) atTop (𝓝 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by positivity : (0 : ℝ) < 1 / 2) s)
      |>.tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp <| tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have hcomp : Tendsto (fun w : ℝ ↦ |w| ^ s * Real.exp (-(1 / 2 : ℝ) * |w| ^ 2))
      (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]; exact hatTop.comp tendsto_comap
  have h := hcomp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  refine h.congr fun w ↦ ?_
  rw [sq_abs, stdNormalPDF_eq]; ring_nf

/-- Rapid decay $\lim_{w \to +\infty} w^n \phi(w) = 0$ (Lemma 2.1 `\label{lem1}`,
`SteinIntro.tex:630-635`). -/
theorem tendsto_pow_mul_stdNormalPDF_atTop (n : ℕ) :
    Tendsto (fun w : ℝ ↦ w ^ n * stdNormalPDF w) atTop (𝓝 0) := by
  have h := (tendsto_rpow_abs_mul_stdNormalPDF_cocompact (n : ℝ)).mono_left atTop_le_cocompact
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
  rw [abs_of_nonneg hw, Real.rpow_natCast]

/-- Decay $\phi(+\infty) = 0$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:630-635`). -/
theorem tendsto_stdNormalPDF_atTop : Tendsto stdNormalPDF atTop (𝓝 0) := by
  simpa using tendsto_pow_mul_stdNormalPDF_atTop 0

/-- Decay $\lim_{w \to +\infty} w \phi(w) = 0$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem tendsto_mul_stdNormalPDF_atTop :
    Tendsto (fun w : ℝ ↦ w * stdNormalPDF w) atTop (𝓝 0) := by
  simpa using tendsto_pow_mul_stdNormalPDF_atTop 1

/-- Integrability of $t \mapsto t \phi(t)$ (Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:628-637`). -/
theorem integrable_mul_stdNormalPDF : Integrable (fun t : ℝ ↦ t * stdNormalPDF t) := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun x ↦ -stdNormalPDF x) (t * stdNormalPDF t) t := by
    intro t _; convert (hasDerivAt_stdNormalPDF t).neg using 1; ring
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t * stdNormalPDF t :=
    fun t ht ↦ mul_nonneg (le_of_lt ht) (stdNormalPDF_nonneg t)
  have hlim : Tendsto (fun x ↦ -stdNormalPDF x) atTop (𝓝 0) := by
    simpa using tendsto_stdNormalPDF_atTop.neg
  have hIoi : IntegrableOn (fun t : ℝ ↦ t * stdNormalPDF t) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hIic : IntegrableOn (fun t : ℝ ↦ t * stdNormalPDF t) (Iic 0) := by
    have hneg : IntegrableOn (fun t : ℝ ↦ (-t) * stdNormalPDF (-t)) (Iio 0) := by
      have hpre : (Neg.neg ⁻¹' Ioi (0 : ℝ)) = Iio 0 := by ext t; simp
      rw [← hpre]
      exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hIoi
    have hIio : IntegrableOn (fun t : ℝ ↦ t * stdNormalPDF t) (Iio 0) := by
      convert hneg.neg using 1; ext t; simp [stdNormalPDF_even]
    exact hIio.congr_set_ae Iio_ae_eq_Iic.symm
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- Tail moment $\int_{(w, \infty)} t \phi(t)\,dt = \phi(w)$ (Lemma 2.1 `\label{lem1}`,
`SteinIntro.tex:628-637`). -/
theorem integral_Ioi_mul_stdNormalPDF (w : ℝ) :
    ∫ t in Ioi w, t * stdNormalPDF t = stdNormalPDF w := by
  have hderiv : ∀ t ∈ Ici w,
      HasDerivAt (fun x ↦ -stdNormalPDF x) (t * stdNormalPDF t) t := by
    intro t _; convert (hasDerivAt_stdNormalPDF t).neg using 1; ring
  have hlim : Tendsto (fun x ↦ -stdNormalPDF x) atTop (𝓝 0) := by
    simpa using tendsto_stdNormalPDF_atTop.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    integrable_mul_stdNormalPDF.integrableOn hlim]; ring

/-! ### Section 2: Mill's Ratio Tail Decay and First-Order Stein Kernels -/

/-- Mill's ratio upper bound $w (1 - \Phi(w)) \le \phi(w)$ (Lemma 2.2 `\label{lem2}`,
`SteinIntro.tex:620-622`; Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:686-694`). -/
theorem mul_one_sub_stdNormalCDF_le (w : ℝ) (_ : 0 ≤ w) :
    w * (1 - stdNormalCDF w) ≤ stdNormalPDF w := by
  rw [one_sub_stdNormalCDF_eq_integral_Ioi, ← integral_const_mul,
    ← integral_Ioi_mul_stdNormalPDF w]
  refine setIntegral_mono_on (integrable_stdNormalPDF.const_mul w).integrableOn
    integrable_mul_stdNormalPDF.integrableOn measurableSet_Ioi fun t ht ↦ ?_
  exact mul_le_mul_of_nonneg_right (le_of_lt ht) (stdNormalPDF_nonneg t)

/-- Left-tail bound $(-w) \Phi(w) \le \phi(w)$ for $w \le 0$ (Lemma 2.2 `\label{lem2}`,
`SteinIntro.tex:620-622`; Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:686-694`). -/
theorem neg_mul_stdNormalCDF_le (w : ℝ) (hw : w ≤ 0) :
    (-w) * stdNormalCDF w ≤ stdNormalPDF w := by
  have h := mul_one_sub_stdNormalCDF_le (-w) (neg_nonneg.mpr hw)
  rwa [← stdNormalCDF_neg, neg_neg, stdNormalPDF_even] at h

/-- Polynomial-times-tail decay $\lim_{w \to +\infty} w^n (1 - \Phi(w)) = 0$
(Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem tendsto_pow_mul_one_sub_stdNormalCDF_atTop (n : ℕ) :
    Tendsto (fun w : ℝ ↦ w ^ n * (1 - stdNormalCDF w)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_pow_mul_stdNormalPDF_atTop n) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
    exact mul_nonneg (pow_nonneg hw n) (sub_nonneg.mpr (stdNormalCDF_le_one w))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with w hw
    have hw0 : 0 ≤ w := zero_le_one.trans hw
    have htail : 1 - stdNormalCDF w ≤ stdNormalPDF w := by
      calc 1 - stdNormalCDF w
          = 1 * (1 - stdNormalCDF w) := (one_mul _).symm
        _ ≤ w * (1 - stdNormalCDF w) :=
            mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr (stdNormalCDF_le_one w))
        _ ≤ stdNormalPDF w := mul_one_sub_stdNormalCDF_le w hw0
    exact mul_le_mul_of_nonneg_left htail (pow_nonneg hw0 n)

/-- Decay $\lim_{w \to +\infty} w (1 - \Phi(w)) = 0$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem tendsto_mul_one_sub_stdNormalCDF_atTop :
    Tendsto (fun w : ℝ ↦ w * (1 - stdNormalCDF w)) atTop (𝓝 0) := by
  simpa using tendsto_pow_mul_one_sub_stdNormalCDF_atTop 1

/-- Decay $\lim_{w \to +\infty} w^2 (1 - \Phi(w)) = 0$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem tendsto_sq_mul_one_sub_stdNormalCDF_atTop :
    Tendsto (fun w : ℝ ↦ w ^ 2 * (1 - stdNormalCDF w)) atTop (𝓝 0) :=
  tendsto_pow_mul_one_sub_stdNormalCDF_atTop 2

/-- Kernel $A(w) = \phi(w) + w \Phi(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
noncomputable def steinKernelA (w : ℝ) : ℝ := stdNormalPDF w + w * stdNormalCDF w

/-- Right Green's kernel $B(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
noncomputable def steinKernelB (w : ℝ) : ℝ := stdNormalPDF w - w * (1 - stdNormalCDF w)

/-- Reflection $B(w) = A(-w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem steinKernelB_eq_neg (w : ℝ) : steinKernelB w = steinKernelA (-w) := by
  simp only [steinKernelA, steinKernelB, stdNormalPDF_even, stdNormalCDF_neg]; ring

/-- Reflection $A(w) = B(-w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem steinKernelA_eq_neg (w : ℝ) : steinKernelA w = steinKernelB (-w) := by
  rw [steinKernelB_eq_neg, neg_neg]

/-- Derivative $A'(w) = \Phi(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem hasDerivAt_steinKernelA (w : ℝ) :
    HasDerivAt steinKernelA (stdNormalCDF w) w := by
  unfold steinKernelA
  convert (hasDerivAt_stdNormalPDF w).add ((hasDerivAt_id' w).mul (hasDerivAt_stdNormalCDF w))
    using 1; ring

/-- Derivative $B'(w) = -(1 - \Phi(w))$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem hasDerivAt_steinKernelB (w : ℝ) :
    HasDerivAt steinKernelB (-(1 - stdNormalCDF w)) w := by
  unfold steinKernelB
  have h1 : HasDerivAt (fun x ↦ 1 - stdNormalCDF x) (-stdNormalPDF w) w := by
    simpa using (hasDerivAt_stdNormalCDF w).const_sub 1
  convert (hasDerivAt_stdNormalPDF w).sub ((hasDerivAt_id' w).mul h1) using 1; ring

private theorem tendsto_steinKernelB_atTop : Tendsto steinKernelB atTop (𝓝 0) := by
  unfold steinKernelB
  simpa using tendsto_stdNormalPDF_atTop.sub tendsto_mul_one_sub_stdNormalCDF_atTop

private theorem strictAnti_steinKernelB : StrictAnti steinKernelB :=
  strictAnti_of_hasDerivAt_neg hasDerivAt_steinKernelB fun w ↦
    neg_lt_zero.mpr (sub_pos.mpr (stdNormalCDF_lt_one w))

/-- Strict positivity $0 < B(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem steinKernelB_pos (w : ℝ) : 0 < steinKernelB w := by
  have hlt : steinKernelB (w + 1) < steinKernelB w := strictAnti_steinKernelB (by linarith)
  have hnonneg : 0 ≤ steinKernelB (w + 1) := by
    refine le_of_tendsto tendsto_steinKernelB_atTop ?_
    filter_upwards [eventually_ge_atTop (w + 1)] with t ht
    exact strictAnti_steinKernelB.antitone ht
  exact lt_of_le_of_lt hnonneg hlt

/-- Strict positivity $0 < A(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem steinKernelA_pos (w : ℝ) : 0 < steinKernelA w := by
  rw [steinKernelA_eq_neg]; exact steinKernelB_pos (-w)

/-- Nonnegativity $0 \le B(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem steinKernelB_nonneg (w : ℝ) : 0 ≤ steinKernelB w := (steinKernelB_pos w).le

/-- Nonnegativity $0 \le A(w)$ (Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem steinKernelA_nonneg (w : ℝ) : 0 ≤ steinKernelA w := (steinKernelA_pos w).le

private theorem hasDerivAt_neg_steinKernelB (s : ℝ) :
    HasDerivAt (fun x ↦ -steinKernelB x) (1 - stdNormalCDF s) s := by
  convert (hasDerivAt_steinKernelB s).neg using 1; ring

/-- Integrability of $1 - \Phi$ on $(w, \infty)$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem integrableOn_Ioi_one_sub_stdNormalCDF (w : ℝ) :
    IntegrableOn (fun s ↦ 1 - stdNormalCDF s) (Ioi w) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ ↦ hasDerivAt_neg_steinKernelB s)
    (fun s _ ↦ sub_nonneg.mpr (cdf_le_one _ s))
    (by simpa using tendsto_steinKernelB_atTop.neg)

/-- Right-tail integral $\int_{(w, \infty)} (1 - \Phi) = B(w)$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem integral_Ioi_one_sub_stdNormalCDF (w : ℝ) :
    ∫ s in Ioi w, (1 - stdNormalCDF s) = steinKernelB w := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ ↦ hasDerivAt_neg_steinKernelB s)
    (fun s _ ↦ sub_nonneg.mpr (cdf_le_one _ s))
    (by simpa using tendsto_steinKernelB_atTop.neg)]; ring

/-- Integrability of $\Phi$ on $(-\infty, w]$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem integrableOn_Iic_stdNormalCDF (w : ℝ) :
    IntegrableOn stdNormalCDF (Iic w) := by
  have hneg : IntegrableOn (fun s ↦ 1 - stdNormalCDF (-s)) (Iio w) := by
    have hpre : (Neg.neg ⁻¹' Ioi (-w)) = Iio w := by ext s; simp
    rw [← hpre]
    exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mpr (integrableOn_Ioi_one_sub_stdNormalCDF (-w))
  have hIio : IntegrableOn stdNormalCDF (Iio w) := by
    refine hneg.congr_fun (fun s _ ↦ ?_) measurableSet_Iio
    dsimp; rw [stdNormalCDF_neg, sub_sub_cancel]
  exact hIio.congr_set_ae Iio_ae_eq_Iic.symm

/-- Left-tail integral $\int_{(-\infty, w]} \Phi = A(w)$ (Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:690-694`). -/
theorem integral_Iic_stdNormalCDF (w : ℝ) :
    ∫ s in Iic w, stdNormalCDF s = steinKernelA w := by
  rw [steinKernelA_eq_neg, ← integral_Ioi_one_sub_stdNormalCDF (-w)]
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (fun s ↦ 1 - stdNormalCDF s) (Ioi (-w))
  have hpre : (Neg.neg ⁻¹' Ioi (-w)) = Iio w := by ext s; simp
  rw [← hneg, hpre, ← setIntegral_congr_set Iio_ae_eq_Iic]
  refine setIntegral_congr_fun measurableSet_Iio fun s _ ↦ ?_
  rw [stdNormalCDF_neg, sub_sub_cancel]

private theorem strictAnti_millRatio :
    StrictAnti (fun w : ℝ ↦ (1 - stdNormalCDF w) / stdNormalPDF w) := by
  refine strictAnti_of_hasDerivAt_neg (f' := fun w ↦ -steinKernelB w / stdNormalPDF w)
    (fun w ↦ ?_) (fun w ↦ ?_)
  · have h1 : HasDerivAt (fun x ↦ 1 - stdNormalCDF x) (-stdNormalPDF w) w := by
      simpa using (hasDerivAt_stdNormalCDF w).const_sub 1
    have hne : stdNormalPDF w ≠ 0 := (stdNormalPDF_pos w).ne'
    convert h1.div (hasDerivAt_stdNormalPDF w) hne using 1
    unfold steinKernelB; field_simp [hne]; ring
  · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (steinKernelB_pos w)) (stdNormalPDF_pos w)

private theorem millRatio_zero :
    (1 - stdNormalCDF 0) / stdNormalPDF 0 = Real.sqrt (Real.pi / 2) := by
  rw [stdNormalCDF_zero, stdNormalPDF_zero]
  have hsq : ((1 - (1 : ℝ) / 2) / (Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = Real.pi / 2 := by
    have hpos : 0 ≤ 2 * Real.pi := by positivity
    field_simp; rw [Real.sq_sqrt hpos]; ring
  have hnonneg : 0 ≤ (1 - (1 : ℝ) / 2) / (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  rw [← Real.sqrt_sq hnonneg, hsq]

/-- Mill's ratio bound $(1 - \Phi(w)) / \phi(w) \le \sqrt{\pi / 2}$ for $w \ge 0$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:620-622`; Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:686-689`). -/
theorem one_sub_stdNormalCDF_div_stdNormalPDF_le (w : ℝ) (hw : 0 ≤ w) :
    (1 - stdNormalCDF w) / stdNormalPDF w ≤ Real.sqrt (Real.pi / 2) := by
  rw [← millRatio_zero]; exact strictAnti_millRatio.antitone hw

/-- Left Mill's ratio bound $\Phi(w) / \phi(w) \le \sqrt{\pi / 2}$ for $w \le 0$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:620-622`; Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:686-689`). -/
theorem stdNormalCDF_div_stdNormalPDF_le (w : ℝ) (hw : w ≤ 0) :
    stdNormalCDF w / stdNormalPDF w ≤ Real.sqrt (Real.pi / 2) := by
  have h := one_sub_stdNormalCDF_div_stdNormalPDF_le (-w) (neg_nonneg.mpr hw)
  rwa [stdNormalCDF_neg, sub_sub_cancel, stdNormalPDF_even] at h

/-- Right-tail Gaussian factor as $(1 - \Phi(w)) / \phi(w)$ (Lemma 2.2 `\label{lem2}`,
`SteinIntro.tex:584-587`, `620-622`). -/
theorem exp_mul_integral_Ioi_exp_eq_div (w : ℝ) :
    Real.exp (w ^ 2 / 2) * ∫ t in Ioi w, Real.exp (-t ^ 2 / 2) =
      (1 - stdNormalCDF w) / stdNormalPDF w := by
  rw [integral_Ioi_exp_neg_sq_div_two, stdNormalPDF_eq]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hexp : Real.exp (-w ^ 2 / 2) = (Real.exp (w ^ 2 / 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [hexp]; field_simp [hsqrt]

/-- Left-tail Gaussian factor as $\Phi(w) / \phi(w)$ (Lemma 2.2 `\label{lem2}`,
`SteinIntro.tex:584-587`, `620-622`). -/
theorem exp_mul_integral_Iic_exp_eq_div (w : ℝ) :
    Real.exp (w ^ 2 / 2) * ∫ t in Iic w, Real.exp (-t ^ 2 / 2) =
      stdNormalCDF w / stdNormalPDF w := by
  rw [integral_Iic_exp_neg_sq_div_two, stdNormalPDF_eq]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hexp : Real.exp (-w ^ 2 / 2) = (Real.exp (w ^ 2 / 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [hexp]; field_simp [hsqrt]

/-- Right-tail Gaussian factor bound $e^{w^2/2} \int_{(w, \infty)} e^{-t^2/2}\,dt \le \sqrt{\pi/2}$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:620-622`; Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:686-689`). -/
theorem exp_mul_integral_Ioi_exp_le_sqrt_pi_div_two (w : ℝ) (hw : 0 ≤ w) :
    Real.exp (w ^ 2 / 2) * ∫ t in Ioi w, Real.exp (-t ^ 2 / 2) ≤ Real.sqrt (Real.pi / 2) := by
  rw [exp_mul_integral_Ioi_exp_eq_div]; exact one_sub_stdNormalCDF_div_stdNormalPDF_le w hw

/-- Left-tail Gaussian factor bound $e^{w^2/2} \int_{(-\infty, w]} e^{-t^2/2}\,dt \le \sqrt{\pi/2}$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:620-622`; Lemma 2.5 `\label{lem31}`,
`SteinIntro.tex:686-689`). -/
theorem exp_mul_integral_Iic_exp_le_sqrt_pi_div_two (w : ℝ) (hw : w ≤ 0) :
    Real.exp (w ^ 2 / 2) * ∫ t in Iic w, Real.exp (-t ^ 2 / 2) ≤ Real.sqrt (Real.pi / 2) := by
  rw [exp_mul_integral_Iic_exp_eq_div]; exact stdNormalCDF_div_stdNormalPDF_le w hw

/-- Weighted right-tail bound $w e^{w^2/2} \int_{(w, \infty)} e^{-t^2/2}\,dt \le 1$ for $w \ge 0$
(Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:686-689`). -/
theorem mul_exp_mul_integral_Ioi_exp_le_one (w : ℝ) (hw : 0 ≤ w) :
    w * (Real.exp (w ^ 2 / 2) * ∫ t in Ioi w, Real.exp (-t ^ 2 / 2)) ≤ 1 := by
  rw [exp_mul_integral_Ioi_exp_eq_div, ← mul_div_assoc, div_le_one₀ (stdNormalPDF_pos w)]
  exact mul_one_sub_stdNormalCDF_le w hw

/-- Weighted left-tail bound $(-w) e^{w^2/2} \int_{(-\infty, w]} e^{-t^2/2}\,dt \le 1$ for $w \le 0$
(Lemma 2.5 `\label{lem31}`, `SteinIntro.tex:686-689`). -/
theorem neg_mul_exp_mul_integral_Iic_exp_le_one (w : ℝ) (hw : w ≤ 0) :
    (-w) * (Real.exp (w ^ 2 / 2) * ∫ t in Iic w, Real.exp (-t ^ 2 / 2)) ≤ 1 := by
  rw [exp_mul_integral_Iic_exp_eq_div, ← mul_div_assoc, div_le_one₀ (stdNormalPDF_pos w)]
  exact neg_mul_stdNormalCDF_le w hw

/-! ### Section 3: Sharp CGS Lemma 2.4 Kernel Bound and Second-Order Tail Positivity -/

section QuadraticSeparator

private noncomputable def sepConst : ℝ := (2 * stdNormalPDF 0)⁻¹

private noncomputable def sepPoly (t : ℝ) : ℝ := 1 + sepConst * t + t ^ 2 / 2

private theorem sepConst_pos : 0 < sepConst :=
  inv_pos.mpr (mul_pos zero_lt_two (stdNormalPDF_pos 0))

private theorem sepPoly_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ sepPoly t := by
  unfold sepPoly; nlinarith [sepConst_pos, sq_nonneg t]

private theorem sepPoly_pos {t : ℝ} (ht : 0 ≤ t) : 0 < sepPoly t :=
  lt_of_lt_of_le zero_lt_one (sepPoly_ge_one ht)

private theorem hasDerivAt_sepPoly (t : ℝ) :
    HasDerivAt sepPoly (sepConst + t) t := by
  unfold sepPoly
  have h1 : HasDerivAt (fun x : ℝ ↦ 1 + sepConst * x) sepConst t := by
    simpa using ((hasDerivAt_id t).const_mul sepConst).const_add 1
  have h2 : HasDerivAt (fun x : ℝ ↦ x ^ 2 / 2) t t := by
    convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
  exact h1.add h2

private theorem steinKernelA_le_mul_sepPoly {w : ℝ} (hw : 0 ≤ w) :
    steinKernelA w ≤ stdNormalPDF 0 * sepPoly w := by
  let u : ℝ → ℝ := fun t ↦ stdNormalPDF 0 * sepPoly t - steinKernelA t
  let u' : ℝ → ℝ := fun t ↦ stdNormalPDF 0 * (sepConst + t) - stdNormalCDF t
  have hu_deriv : ∀ t, HasDerivAt u (u' t) t := fun t ↦
    ((hasDerivAt_sepPoly t).const_mul (stdNormalPDF 0)).sub (hasDerivAt_steinKernelA t)
  have hu'_deriv : ∀ t, HasDerivAt u' (stdNormalPDF 0 - stdNormalPDF t) t := by
    intro t
    have hlin : HasDerivAt (fun x : ℝ ↦ stdNormalPDF 0 * (sepConst + x)) (stdNormalPDF 0) t := by
      convert ((hasDerivAt_id' t).const_add sepConst).const_mul (stdNormalPDF 0) using 1; ring
    exact hlin.sub (hasDerivAt_stdNormalCDF t)
  have hu'_mono : Monotone u' :=
    monotone_of_hasDerivAt_nonneg hu'_deriv fun t ↦ sub_nonneg.mpr (stdNormalPDF_le_zero t)
  have hu'0 : u' 0 = 0 := by
    simp only [u', sepConst, add_zero, stdNormalCDF_zero]
    have h0 : stdNormalPDF 0 ≠ 0 := (stdNormalPDF_pos 0).ne'
    field_simp [h0]; ring
  have hu_mono : MonotoneOn u (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ ↦ (hu_deriv t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hu_deriv t).hasDerivWithinAt) fun t ht ↦ ?_
    rw [interior_Ici] at ht; rw [← hu'0]; exact hu'_mono (le_of_lt ht)
  have hu0 : u 0 = 0 := by simp [u, sepPoly, steinKernelA]
  have hle : u 0 ≤ u w := hu_mono self_mem_Ici hw hw
  rw [hu0] at hle; linarith

private noncomputable def sepDiff (t : ℝ) : ℝ :=
  (1 - stdNormalCDF t) - stdNormalPDF t * (sepConst + t / 2) / sepPoly t

private theorem hasDerivAt_sepDiff {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt sepDiff
      (stdNormalPDF t / (sepPoly t) ^ 2 * ((sepConst ^ 2 - 3 / 2) - t ^ 2 / 4)) t := by
  unfold sepDiff
  have h1 : HasDerivAt (fun x ↦ 1 - stdNormalCDF x) (-stdNormalPDF t) t := by
    simpa using (hasDerivAt_stdNormalCDF t).const_sub 1
  have hlin : HasDerivAt (fun x : ℝ ↦ sepConst + x / 2) (1 / 2) t := by
    simpa using ((hasDerivAt_id t).div_const 2).const_add sepConst
  have hnum : HasDerivAt (fun x ↦ stdNormalPDF x * (sepConst + x / 2))
      ((-t * stdNormalPDF t) * (sepConst + t / 2) + stdNormalPDF t * (1 / 2)) t :=
    (hasDerivAt_stdNormalPDF t).mul hlin
  have hS : sepPoly t ≠ 0 := (sepPoly_pos ht).ne'
  convert h1.sub (hnum.div (hasDerivAt_sepPoly t) hS) using 1
  field_simp [hS]; unfold sepPoly; ring

private theorem tendsto_sepDiff_atTop : Tendsto sepDiff atTop (𝓝 0) := by
  have h1 : Tendsto (fun t ↦ 1 - stdNormalCDF t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_stdNormalCDF_atTop
  have h2 : Tendsto (fun t ↦ stdNormalPDF t * (sepConst + t / 2) / sepPoly t) atTop (𝓝 0) := by
    have hupper : Tendsto (fun t ↦ sepConst * stdNormalPDF t + (1 / 2) * (t * stdNormalPDF t))
        atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (tendsto_stdNormalPDF_atTop.const_mul sepConst).add
        (tendsto_mul_stdNormalPDF_atTop.const_mul (1 / 2))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hc : 0 ≤ sepConst + t / 2 := by linarith [sepConst_pos]
      exact div_nonneg (mul_nonneg (stdNormalPDF_nonneg t) hc) (sepPoly_pos ht).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hS1 : 1 ≤ sepPoly t := sepPoly_ge_one ht
      have hc : 0 ≤ stdNormalPDF t * (sepConst + t / 2) :=
        mul_nonneg (stdNormalPDF_nonneg t) (by linarith [sepConst_pos])
      calc stdNormalPDF t * (sepConst + t / 2) / sepPoly t
          ≤ stdNormalPDF t * (sepConst + t / 2) / 1 :=
            div_le_div_of_nonneg_left hc zero_lt_one hS1
        _ = sepConst * stdNormalPDF t + (1 / 2) * (t * stdNormalPDF t) := by ring
  unfold sepDiff; simpa using h1.sub h2

private theorem sepDiff_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ sepDiff w := by
  have hD0 : sepDiff 0 = 0 := by
    unfold sepDiff sepPoly sepConst
    rw [stdNormalCDF_zero]
    have h0 : stdNormalPDF 0 ≠ 0 := (stdNormalPDF_pos 0).ne'
    field_simp [h0]; ring
  have hcont : ContinuousOn sepDiff (Ici 0) :=
    fun t ht ↦ (hasDerivAt_sepDiff ht).continuousAt.continuousWithinAt
  rcases le_total (w ^ 2 / 4) (sepConst ^ 2 - 3 / 2) with hcase | hcase
  · have hmono : MonotoneOn sepDiff (Icc 0 w) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 w)
        (hcont.mono Icc_subset_Ici_self)
        (fun t ht ↦ (hasDerivAt_sepDiff
          (by rw [interior_Icc] at ht; exact ht.1.le)).hasDerivWithinAt) fun t ht ↦ ?_
      rw [interior_Icc] at ht
      have ht2 : t ^ 2 ≤ w ^ 2 := by nlinarith [ht.1, ht.2]
      have hfac : 0 ≤ (sepConst ^ 2 - 3 / 2) - t ^ 2 / 4 := by linarith
      exact mul_nonneg (div_nonneg (stdNormalPDF_nonneg t) (sq_nonneg _)) hfac
    rw [← hD0]; exact hmono (left_mem_Icc.mpr hw) (right_mem_Icc.mpr hw) hw
  · have hanti : AntitoneOn sepDiff (Ici w) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici w)
        (hcont.mono (Ici_subset_Ici.mpr hw))
        (fun t ht ↦ (hasDerivAt_sepDiff
          (by rw [interior_Ici] at ht; linarith [mem_Ioi.mp ht])).hasDerivWithinAt) fun t ht ↦ ?_
      rw [interior_Ici] at ht
      have hwt : w < t := mem_Ioi.mp ht
      have ht2 : w ^ 2 ≤ t ^ 2 := by nlinarith [hw, hwt]
      have hfac : (sepConst ^ 2 - 3 / 2) - t ^ 2 / 4 ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (stdNormalPDF_nonneg t) (sq_nonneg _)) hfac
    refine le_of_tendsto tendsto_sepDiff_atTop ?_
    filter_upwards [eventually_ge_atTop w] with t ht
    exact hanti self_mem_Ici ht ht

private theorem steinKernelB_mul_sepPoly_le {w : ℝ} (hw : 0 ≤ w) :
    steinKernelB w * sepPoly w ≤ stdNormalPDF w := by
  have hS : sepPoly w ≠ 0 := (sepPoly_pos hw).ne'
  have hid : stdNormalPDF w - steinKernelB w * sepPoly w = w * sepPoly w * sepDiff w := by
    unfold steinKernelB sepDiff; field_simp [hS]; unfold sepPoly; ring
  have hnonneg : 0 ≤ w * sepPoly w * sepDiff w :=
    mul_nonneg (mul_nonneg hw (sepPoly_pos hw).le) (sepDiff_nonneg hw)
  linarith

private theorem two_mul_stdNormalPDF_zero :
    2 * stdNormalPDF 0 = Real.sqrt (2 / Real.pi) := by
  rw [stdNormalPDF_zero]
  have hsq : (2 * (Real.sqrt (2 * Real.pi))⁻¹) ^ 2 = 2 / Real.pi := by
    have hpos : 0 ≤ 2 * Real.pi := by positivity
    have hne : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [mul_pow, inv_pow, Real.sq_sqrt hpos]; field_simp [hne]
  have hnonneg : 0 ≤ 2 * (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  rw [← Real.sqrt_sq hnonneg, hsq]

private theorem two_mul_steinKernelA_mul_steinKernelB_div_le_nonneg {w : ℝ} (hw : 0 ≤ w) :
    2 * steinKernelA w * steinKernelB w / stdNormalPDF w ≤ Real.sqrt (2 / Real.pi) := by
  have hA := steinKernelA_le_mul_sepPoly hw
  have hB := steinKernelB_mul_sepPoly_le hw
  have hBpos := (steinKernelB_pos w).le
  have hprod : 2 * steinKernelA w * steinKernelB w ≤ 2 * stdNormalPDF 0 * stdNormalPDF w := by
    calc 2 * steinKernelA w * steinKernelB w
        ≤ 2 * (stdNormalPDF 0 * sepPoly w) * steinKernelB w := by nlinarith [hA, hBpos]
      _ = 2 * stdNormalPDF 0 * (steinKernelB w * sepPoly w) := by ring
      _ ≤ 2 * stdNormalPDF 0 * stdNormalPDF w :=
          mul_le_mul_of_nonneg_left hB (mul_nonneg zero_le_two (stdNormalPDF_nonneg 0))
  rw [div_le_iff₀ (stdNormalPDF_pos w), ← two_mul_stdNormalPDF_zero]
  exact hprod

private theorem two_mul_steinKernelA_mul_steinKernelB_div_le_aux (w : ℝ) :
    2 * steinKernelA w * steinKernelB w / stdNormalPDF w ≤ Real.sqrt (2 / Real.pi) := by
  rcases le_total 0 w with hw | hw
  · exact two_mul_steinKernelA_mul_steinKernelB_div_le_nonneg hw
  · have h := two_mul_steinKernelA_mul_steinKernelB_div_le_nonneg (neg_nonneg.mpr hw)
    rw [← steinKernelB_eq_neg, ← steinKernelA_eq_neg, stdNormalPDF_even] at h
    convert h using 1; ring

end QuadraticSeparator

/-- Sharp Chen–Goldstein–Shao (2011) Lemma 2.4 first-derivative Green's kernel bound
(Lemma 2.5(2) `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem two_mul_steinKernelA_mul_steinKernelB_div_le (w : ℝ) :
    2 * (stdNormalPDF w + w * stdNormalCDF w) *
      (stdNormalPDF w - w * (1 - stdNormalCDF w)) / stdNormalPDF w ≤
        Real.sqrt (2 / Real.pi) :=
  two_mul_steinKernelA_mul_steinKernelB_div_le_aux w

private noncomputable def secondMomentTail (w : ℝ) : ℝ :=
  (1 + w ^ 2) * (1 - stdNormalCDF w) - w * stdNormalPDF w

private theorem hasDerivAt_secondMomentTail (w : ℝ) :
    HasDerivAt secondMomentTail (-2 * steinKernelB w) w := by
  unfold secondMomentTail
  have h1 : HasDerivAt (fun t : ℝ ↦ 1 + t ^ 2) (2 * w) w := by
    simpa using (hasDerivAt_pow 2 w).const_add 1
  have h2 : HasDerivAt (fun t : ℝ ↦ 1 - stdNormalCDF t) (-stdNormalPDF w) w := by
    simpa using (hasDerivAt_stdNormalCDF w).const_sub 1
  have h3 : HasDerivAt (fun t : ℝ ↦ t * stdNormalPDF t)
      (1 * stdNormalPDF w + w * (-w * stdNormalPDF w)) w :=
    (hasDerivAt_id w).mul (hasDerivAt_stdNormalPDF w)
  convert (h1.mul h2).sub h3 using 1; unfold steinKernelB; ring

private theorem tendsto_secondMomentTail_atTop :
    Tendsto secondMomentTail atTop (𝓝 0) := by
  have h1 : Tendsto (fun w : ℝ ↦ 1 - stdNormalCDF w) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_stdNormalCDF_atTop
  have hsum : Tendsto (fun w : ℝ ↦ (1 - stdNormalCDF w) + w ^ 2 * (1 - stdNormalCDF w) -
      w * stdNormalPDF w) atTop (𝓝 0) := by
    simpa using (h1.add tendsto_sq_mul_one_sub_stdNormalCDF_atTop).sub
      tendsto_mul_stdNormalPDF_atTop
  refine hsum.congr fun w ↦ ?_
  unfold secondMomentTail; ring

private theorem strictAnti_secondMomentTail : StrictAnti secondMomentTail :=
  strictAnti_of_hasDerivAt_neg hasDerivAt_secondMomentTail fun w ↦ by
    linarith [steinKernelB_pos w]

private theorem secondMomentTail_pos (w : ℝ) : 0 < secondMomentTail w := by
  have hlt : secondMomentTail (w + 1) < secondMomentTail w :=
    strictAnti_secondMomentTail (by linarith)
  have hnonneg : 0 ≤ secondMomentTail (w + 1) := by
    refine le_of_tendsto tendsto_secondMomentTail_atTop ?_
    filter_upwards [eventually_ge_atTop (w + 1)] with t ht
    exact strictAnti_secondMomentTail.antitone ht
  exact lt_of_le_of_lt hnonneg hlt

/-- Nonnegativity $0 \le (1 + w^2)(1 - \Phi(w)) - w \phi(w)$ of the second-order right tail factor
(Lemma 2.5(2) `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem one_add_sq_mul_one_sub_stdNormalCDF_sub_nonneg (w : ℝ) :
    0 ≤ (1 + w ^ 2) * (1 - stdNormalCDF w) - w * stdNormalPDF w :=
  (secondMomentTail_pos w).le

/-- Nonnegativity $0 \le (1 + w^2)\Phi(w) + w \phi(w)$ of the second-order left tail factor
(Lemma 2.5(2) `\label{lem31}`, `SteinIntro.tex:690-694`). -/
theorem one_add_sq_mul_stdNormalCDF_add_nonneg (w : ℝ) :
    0 ≤ (1 + w ^ 2) * stdNormalCDF w + w * stdNormalPDF w := by
  have h := one_add_sq_mul_one_sub_stdNormalCDF_sub_nonneg (-w)
  rw [stdNormalCDF_neg, stdNormalPDF_even] at h
  have heq : (1 + (-w) ^ 2) * (1 - (1 - stdNormalCDF w)) - (-w) * stdNormalPDF w =
      (1 + w ^ 2) * stdNormalCDF w + w * stdNormalPDF w := by ring
  rwa [heq] at h

end SteinMethod
