/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.NormalStein
import Formalization.Normal.MillRatio
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Normal Stein Solution Bounds (`Formalization.Normal.SolutionBounds`)

Left-tail representation, differentiability, and uniform solution/derivative estimates for the
normal Stein equation solution `normalSteinSol` (Lemma 2.5 `\label{lem31}`, eq. `(2.6)`
`\label{33}`, items 1–2 `\label{i31}`–`\label{i32}`, `SteinIntro.tex:674-699`), together with the
bounded-continuous Stein solution helper used in the converse direction of Stein's lemma
(Lemma 2.1(2) `\label{lem1}`, `SteinIntro.tex:569-572`, `637-644`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace SteinMethod

/-! ### Section 1: Left-Tail Representation and Differentiability (`Lem2_5_formula`) -/

private lemma exp_neg_half_sq_eq_sqrt_two_pi_mul_pdf (t : ℝ) :
    Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * Real.pi) * stdNormalPDF t := by
  have hpos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  simp only [stdNormalPDF, gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

private lemma integrable_exp_neg_half_sq_mul {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw) :
    Integrable (fun t ↦ Real.exp (-t ^ 2 / 2) * h t) volume := by
  rw [stdNormalLaw, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hInt
  refine (hInt.const_mul (Real.sqrt (2 * Real.pi))).congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [toReal_gaussianPDF, exp_neg_half_sq_eq_sqrt_two_pi_mul_pdf, stdNormalPDF]
  ring

private lemma integral_exp_neg_half_sq_mul {h : ℝ → ℝ} :
    (∫ t, Real.exp (-t ^ 2 / 2) * h t) = Real.sqrt (2 * Real.pi) * stdNormalExpect h := by
  unfold stdNormalExpect
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [exp_neg_half_sq_eq_sqrt_two_pi_mul_pdf, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

private lemma integrable_stein_integrand {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw) :
    Integrable (fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) volume := by
  refine ((integrable_exp_neg_sq_div_two.mul_const (stdNormalExpect h)).sub
    (integrable_exp_neg_half_sq_mul hInt)).congr (ae_of_all _ fun t ↦ ?_)
  simp only [Pi.sub_apply]; ring

private lemma integral_stein_integrand_eq_zero {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw) :
    (∫ t, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) = 0 := by
  have h1 := integrable_exp_neg_sq_div_two.mul_const (stdNormalExpect h)
  have h2 := integrable_exp_neg_half_sq_mul hInt
  have heq : (fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) =
      fun t ↦ Real.exp (-t ^ 2 / 2) * stdNormalExpect h - Real.exp (-t ^ 2 / 2) * h t := by
    ext t; ring
  rw [heq, integral_sub h1 h2, integral_mul_const, integral_exp_neg_sq_div_two,
    integral_exp_neg_half_sq_mul]
  ring

private lemma setIntegral_Iic_eq_add_intervalIntegral {g : ℝ → ℝ}
    (hg : Integrable g volume) (a u : ℝ) :
    (∫ t in Set.Iic u, g t) = (∫ t in Set.Iic a, g t) + ∫ t in a..u, g t := by
  have hdisj : ∀ x y : ℝ, Disjoint (Set.Iic x) (Set.Ioc x y) :=
    fun x y ↦ Set.disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1 h2.1
  rcases le_total a u with hau | hua
  · rw [intervalIntegral.integral_of_le hau,
      ← setIntegral_union (hdisj a u) measurableSet_Ioc hg.integrableOn hg.integrableOn,
      Iic_union_Ioc_eq_Iic hau]
  · rw [intervalIntegral.integral_of_ge hua]
    have hunion := setIntegral_union (hdisj u a) measurableSet_Ioc
      (f := g) hg.integrableOn hg.integrableOn
    rw [Iic_union_Ioc_eq_Iic hua] at hunion
    linarith

/-- Left-tail integral representation
$f_h(w) = -e^{w^2/2} \int_{-\infty}^w e^{-t^2/2}(\Phi(h) - h(t))\,dt$ of the normal Stein equation
solution (Lemma 2.5 `\label{lem31}`, eq. `(2.6)` `\label{33}`, `SteinIntro.tex:674-684`). -/
theorem normalSteinSol_eq_neg_integral_Iic {h : ℝ → ℝ}
    (hInt : Integrable h stdNormalLaw) (w : ℝ) :
    normalSteinSol h w =
      -Real.exp (w ^ 2 / 2) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t) := by
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  have hsum : (∫ t in Set.Iic w, g t) + (∫ t in Set.Ioi w, g t) = 0 := by
    rw [← compl_Iic, integral_add_compl measurableSet_Iic (integrable_stein_integrand hInt)]
    exact integral_stein_integrand_eq_zero hInt
  have hIoi : (∫ t in Set.Ioi w, g t) = -∫ t in Set.Iic w, g t := by linarith
  simp only [normalSteinSol, g] at hIoi ⊢
  rw [hIoi]; ring

private lemma hasDerivAt_exp_half_sq (w : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (u ^ 2 / 2)) (w * Real.exp (w ^ 2 / 2)) w := by
  have h1 : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) w w := by
    convert (hasDerivAt_pow 2 w).div_const 2 using 1; ring
  convert h1.exp using 1; ring

private lemma exp_half_sq_mul_neg (w : ℝ) :
    Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) = 1 := by
  rw [← Real.exp_add]; ring_nf; exact Real.exp_zero

private lemma stein_prod_deriv_alg {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw) (w : ℝ) :
    (-(w * Real.exp (w ^ 2 / 2)) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) +
      -Real.exp (w ^ 2 / 2) * (Real.exp (-w ^ 2 / 2) * (stdNormalExpect h - h w)) =
      w * normalSteinSol h w + h w - stdNormalExpect h := by
  set c := stdNormalExpect h
  set g := fun t ↦ Real.exp (-t ^ 2 / 2) * (c - h t)
  have hfw : normalSteinSol h w = -Real.exp (w ^ 2 / 2) * ∫ t in Set.Iic w, g t :=
    normalSteinSol_eq_neg_integral_Iic hInt w
  calc
    -(w * Real.exp (w ^ 2 / 2)) * (∫ t in Set.Iic w, g t) + -Real.exp (w ^ 2 / 2) * g w
      = w * (-Real.exp (w ^ 2 / 2) * ∫ t in Set.Iic w, g t) -
          (Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2)) * (c - h w) := by simp only [g]; ring
    _ = w * normalSteinSol h w + h w - c := by rw [← hfw, exp_half_sq_mul_neg]; ring

private lemma continuous_normalSteinSol {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw) :
    Continuous (normalSteinSol h) := by
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  have hg := integrable_stein_integrand hInt
  have heq : normalSteinSol h =
      fun w ↦ -Real.exp (w ^ 2 / 2) * ((∫ t in Set.Iic 0, g t) + ∫ t in (0 : ℝ)..w, g t) := by
    ext w
    rw [normalSteinSol_eq_neg_integral_Iic hInt w, setIntegral_Iic_eq_add_intervalIntegral hg 0 w]
  rw [heq]
  exact (by fun_prop : Continuous fun w : ℝ ↦ -Real.exp (w ^ 2 / 2)).mul
    (continuous_const.add (hg.continuous_primitive 0))

private lemma locallyAC_normalSteinSol {h : ℝ → ℝ}
    (hInt : Integrable h stdNormalLaw) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (normalSteinSol h) a b := by
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  have hg := integrable_stein_integrand hInt
  have heq : normalSteinSol h =
      fun x ↦ -Real.exp (x ^ 2 / 2) * ((∫ t in Set.Iic a, g t) + ∫ t in a..x, g t) := by
    ext x
    rw [normalSteinSol_eq_neg_integral_Iic hInt x, setIntegral_Iic_eq_add_intervalIntegral hg a x]
  rw [heq]
  exact ((by fun_prop : ContDiff ℝ 1 fun x : ℝ ↦ -Real.exp (x ^ 2 / 2)).contDiffOn
    |>.absolutelyContinuousOnInterval).mul
    (((LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hg.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc))

/-- Pointwise two-sided derivative $f_h'(w) = w f_h(w) + h(w) - \Phi(h)$ of `normalSteinSol h`
at any point `w` where `h` is continuous (Lemma 2.5 `\label{lem31}`, eq. `(2.6)` `\label{33}`,
`SteinIntro.tex:674-684`). -/
theorem hasDerivAt_normalSteinSol {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw) {w : ℝ}
    (hCont : ContinuousAt h w) :
    HasDerivAt (normalSteinSol h) (w * normalSteinSol h w + h w - stdNormalExpect h) w := by
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  have hg := integrable_stein_integrand hInt
  have hgc : ContinuousAt g w :=
    (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-t ^ 2 / 2)).continuousAt.mul
      (continuousAt_const.sub hCont)
  have hI : HasDerivAt (fun u ↦ ∫ t in Set.Iic u, g t) (g w) w := by
    rw [funext (setIntegral_Iic_eq_add_intervalIntegral hg 0)]
    simpa using (intervalIntegral.integral_hasDerivAt_right hg.intervalIntegrable
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hgc).const_add (∫ t in Set.Iic 0, g t)
  have hprod := (hasDerivAt_exp_half_sq w).fun_neg.fun_mul hI
  rw [← funext (normalSteinSol_eq_neg_integral_Iic hInt)] at hprod
  exact hprod.congr_deriv (stein_prod_deriv_alg hInt w)

/-- Global two-sided derivative $f_h'(w) = w f_h(w) + h(w) - \Phi(h)$ of `normalSteinSol h`
when `h` is continuous and `stdNormalLaw`-integrable (Lemma 2.5 `\label{lem31}`, eq. `(2.6)`
`\label{33}`, `SteinIntro.tex:674-684`). -/
theorem hasDerivAt_normalSteinSol_of_continuous {h : ℝ → ℝ} (hInt : Integrable h stdNormalLaw)
    (hCont : Continuous h) (w : ℝ) :
    HasDerivAt (normalSteinSol h) (w * normalSteinSol h w + h w - stdNormalExpect h) w :=
  hasDerivAt_normalSteinSol hInt hCont.continuousAt

/-! ### Section 2: Bounded Measurable Test Functions (`Lem2_5_1`) -/

private lemma lipschitzWith_of_ac_ae_deriv_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hae : ∀ᵐ u : ℝ, ‖deriv f u‖ ≤ C) :
    LipschitzWith (Real.toNNReal C) f := by
  rw [lipschitzWith_iff_dist_le_mul]
  have hstep : ∀ a b : ℝ, a ≤ b → |f b - f a| ≤ C * (b - a) := by
    intro a b hab
    rw [← (hac a b).integral_deriv_eq_sub, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
    have hb := norm_setIntegral_le_of_norm_le_const_ae
      (s := Set.Ioc a b) measure_Ioc_lt_top (ae_restrict_of_ae hae)
    simpa [Real.volume_real_Ioc_of_le hab, mul_comm] using hb
  intro x y
  rw [Real.coe_toNNReal C hC, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm (f x), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hstep x y hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hstep y x hyx

private lemma integrable_of_abs_sub_stdNormalExpect_le {h : ℝ → ℝ} (hMeas : Measurable h)
    {M : ℝ} (hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ M) :
    Integrable h stdNormalLaw := by
  refine Integrable.of_bound hMeas.aestronglyMeasurable (M + |stdNormalExpect h|)
    (ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (h t) (stdNormalExpect h), hM t]

private lemma abs_setIntegral_stein_integrand_le {h : ℝ → ℝ}
    {M : ℝ} (hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ M) (s : Set ℝ) :
    |∫ t in s, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)| ≤
      (∫ t in s, Real.exp (-t ^ 2 / 2)) * M := by
  rw [← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (integrable_exp_neg_sq_div_two.integrableOn.mul_const M)
    (ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (hM t) (Real.exp_pos _).le

/-- Uniform supremum bound $|f_h(w)| \le \sqrt{\pi/2}\,M$ for measurable `h` with
$|h(t) - \Phi(h)| \le M$ (Lemma 2.5(1) `\label{lem31}` `\label{i31}`,
`SteinIntro.tex:686-689`). -/
theorem abs_normalSteinSol_le_of_bounded {h : ℝ → ℝ} (hMeas : Measurable h) {M : ℝ}
    (hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ M) (w : ℝ) :
    |normalSteinSol h w| ≤ Real.sqrt (Real.pi / 2) * M := by
  have hInt := integrable_of_abs_sub_stdNormalExpect_le hMeas hM
  have hM_nn : 0 ≤ M := (abs_nonneg (h 0 - stdNormalExpect h)).trans (hM 0)
  have hexp_nn : 0 ≤ Real.exp (w ^ 2 / 2) := (Real.exp_pos _).le
  rcases le_total 0 w with hw | hw
  · simp only [normalSteinSol]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine (mul_le_mul_of_nonneg_left
      (abs_setIntegral_stein_integrand_le hM (Set.Ioi w)) hexp_nn).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (exp_mul_integral_Ioi_exp_le_sqrt_pi_div_two w hw) hM_nn
  · rw [normalSteinSol_eq_neg_integral_Iic hInt w, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    refine (mul_le_mul_of_nonneg_left
      (abs_setIntegral_stein_integrand_le hM (Set.Iic w)) hexp_nn).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (exp_mul_integral_Iic_exp_le_sqrt_pi_div_two w hw) hM_nn

/-- Uniform weighted bound $|w f_h(w)| \le M$ for measurable `h` with
$|h(t) - \Phi(h)| \le M$ (Lemma 2.5(1) `\label{lem31}` `\label{i31}`,
`SteinIntro.tex:686-689`). -/
theorem abs_mul_normalSteinSol_le_of_bounded {h : ℝ → ℝ} (hMeas : Measurable h) {M : ℝ}
    (hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ M) (w : ℝ) :
    |w * normalSteinSol h w| ≤ M := by
  have hInt := integrable_of_abs_sub_stdNormalExpect_le hMeas hM
  have hM_nn : 0 ≤ M := (abs_nonneg (h 0 - stdNormalExpect h)).trans (hM 0)
  have hexp_nn : 0 ≤ Real.exp (w ^ 2 / 2) := (Real.exp_pos (w ^ 2 / 2)).le
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  rcases le_total 0 w with hw | hw
  · simp only [normalSteinSol]
    rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_pos (Real.exp_pos _)]
    calc w * (Real.exp (w ^ 2 / 2) * |∫ t in Set.Ioi w, g t|)
      _ ≤ w * (Real.exp (w ^ 2 / 2) * ((∫ t in Set.Ioi w, Real.exp (-t ^ 2 / 2)) * M)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (abs_setIntegral_stein_integrand_le hM (Set.Ioi w)) hexp_nn) hw
      _ = (w * (Real.exp (w ^ 2 / 2) * ∫ t in Set.Ioi w, Real.exp (-t ^ 2 / 2))) * M := by ring
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (mul_exp_mul_integral_Ioi_exp_le_one w hw) hM_nn
      _ = M := one_mul M
  · rw [normalSteinSol_eq_neg_integral_Iic hInt w, abs_mul, abs_mul, abs_neg,
      abs_of_nonpos hw, abs_of_pos (Real.exp_pos _)]
    calc -w * (Real.exp (w ^ 2 / 2) * |∫ t in Set.Iic w, g t|)
      _ ≤ -w * (Real.exp (w ^ 2 / 2) * ((∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2)) * M)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (abs_setIntegral_stein_integrand_le hM (Set.Iic w)) hexp_nn) (neg_nonneg.mpr hw)
      _ = ((-w) * (Real.exp (w ^ 2 / 2) * ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2))) * M := by ring
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (neg_mul_exp_mul_integral_Iic_exp_le_one w hw) hM_nn
      _ = M := one_mul M

/-- Uniform derivative bound $|f_h'(w)| \le 2 M$ for measurable `h` with
$|h(t) - \Phi(h)| \le M$ (Lemma 2.5(1) `\label{lem31}` `\label{i31}`,
`SteinIntro.tex:686-689`). -/
theorem abs_deriv_normalSteinSol_le_of_bounded {h : ℝ → ℝ} (hMeas : Measurable h) {M : ℝ}
    (hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ M) (w : ℝ) :
    |deriv (normalSteinSol h) w| ≤ 2 * M := by
  have hInt := integrable_of_abs_sub_stdNormalExpect_le hMeas hM
  have hM_nn : 0 ≤ M := (abs_nonneg (h 0 - stdNormalExpect h)).trans (hM 0)
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  have hg := integrable_stein_integrand hInt
  have hae_bound : ∀ᵐ u : ℝ, ‖deriv (normalSteinSol h) u‖ ≤ 2 * M := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with u hu
    have hI : HasDerivAt (fun x ↦ ∫ t in Set.Iic x, g t) (g u) u := by
      rw [funext (setIntegral_Iic_eq_add_intervalIntegral hg 0)]
      simpa using (hu 0).const_add (∫ t in Set.Iic 0, g t)
    have hprod := ((hasDerivAt_exp_half_sq u).fun_neg).fun_mul hI
    rw [← funext (normalSteinSol_eq_neg_integral_Iic hInt)] at hprod
    have hdu := (hprod.congr_deriv (stein_prod_deriv_alg hInt u)).deriv
    rw [Real.norm_eq_abs, hdu, add_sub_assoc]
    linarith [abs_add_le (u * normalSteinSol h u) (h u - stdNormalExpect h),
      abs_mul_normalSteinSol_le_of_bounded hMeas hM u, hM u]
  have hlip := lipschitzWith_of_ac_ae_deriv_le (by positivity : 0 ≤ 2 * M)
    (locallyAC_normalSteinSol hInt) hae_bound
  simpa [Real.norm_eq_abs, Real.coe_toNNReal (2 * M) (by positivity)] using
    norm_deriv_le_of_lipschitz (x₀ := w) hlip

/-! ### Section 3: Absolutely Continuous Test Functions (`Lem2_5_2`) -/

private lemma integral_Ioi_one_sub_cdf_eq (w : ℝ) :
    (∫ s in Set.Ioi w, (1 - stdNormalCDF s)) = stdNormalPDF w - w * (1 - stdNormalCDF w) :=
  integral_Ioi_one_sub_stdNormalCDF w

private lemma integral_Iic_cdf_eq (w : ℝ) :
    (∫ s in Set.Iic w, stdNormalCDF s) = stdNormalPDF w + w * stdNormalCDF w :=
  integral_Iic_stdNormalCDF w

private lemma abs_comb_le {a b I1 I2 B1 B2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : |I1| ≤ B1) (h2 : |I2| ≤ B2) :
    |a * I1 - b * I2| ≤ a * B1 + b * B2 ∧ |-a * I1 - b * I2| ≤ a * B1 + b * B2 := by
  have hle1 := mul_le_mul_of_nonneg_left h1 ha
  have hle2 := mul_le_mul_of_nonneg_left h2 hb
  constructor
  · calc |a * I1 - b * I2| ≤ |a * I1| + |b * I2| := abs_sub _ _
      _ = a * |I1| + b * |I2| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B1 + b * B2 := add_le_add hle1 hle2
  · calc |-a * I1 - b * I2| ≤ |-a * I1| + |b * I2| := abs_sub _ _
      _ = a * |I1| + b * |I2| := by
          rw [neg_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B1 + b * B2 := add_le_add hle1 hle2

private lemma normalSteinSol_ac_estimates {h : ℝ → ℝ} {L : ℝ}
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hL : ∀ t : ℝ, |deriv h t| ≤ L) :
    (∀ w : ℝ, |normalSteinSol h w| ≤ 2 * L) ∧
    (∀ w : ℝ, |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi) * L) ∧
    (∀ w : ℝ, |deriv (deriv (normalSteinSol h)) w| ≤ 2 * L) := by
  have hL_nn : 0 ≤ L := (abs_nonneg (deriv h 0)).trans (hL 0)
  have hlip_h := lipschitzWith_of_ac_ae_deriv_le hL_nn hac
    (ae_of_all _ fun t ↦ by rw [Real.norm_eq_abs]; exact hL t)
  have hcont_h : Continuous h := hlip_h.continuous
  have hid_gauss : Integrable id stdNormalLaw :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  have hh_int : Integrable h stdNormalLaw := by
    refine ((integrable_const |h 0|).add (hid_gauss.norm.const_mul L)).mono'
      hcont_h.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    have hd := hlip_h.dist_le_mul t 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero, Real.coe_toNNReal L hL_nn] at hd
    dsimp only [Pi.add_apply, id_eq]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (h t) (h 0)]
  have hderiv_eq : ∀ w : ℝ,
      deriv (normalSteinSol h) w = w * normalSteinSol h w + (h w - stdNormalExpect h) := fun w ↦ by
    rw [(hasDerivAt_normalSteinSol hh_int hcont_h.continuousAt).deriv, add_sub_assoc]
  have hmeas_dh : AEStronglyMeasurable (deriv h) volume := aestronglyMeasurable_deriv h volume
  have hint_pdf_id : Integrable (fun s : ℝ ↦ stdNormalPDF s * |s|) volume := by
    refine ((integrable_exp_neg_half_sq_mul hid_gauss.norm).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹).congr (ae_of_all _ fun s ↦ ?_)
    dsimp only; rw [exp_neg_half_sq_eq_sqrt_two_pi_mul_pdf, Real.norm_eq_abs, id_eq]
    have : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  have hint_pdf_sub : ∀ w : ℝ, Integrable (fun s ↦ stdNormalPDF s * (h s - h w)) volume := by
    intro w
    refine ((hint_pdf_id.const_mul L).add
      ((integrable_gaussianPDFReal 0 1).const_mul (L * |w|))).mono'
      (continuous_stdNormalPDF.mul (hcont_h.sub continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun s ↦ ?_)
    have hd := hlip_h.dist_le_mul s w
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL_nn] at hd
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (stdNormalPDF_pos s)]
    calc stdNormalPDF s * |h s - h w|
      _ ≤ stdNormalPDF s * (L * (|s| + |w|)) :=
        mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left (abs_sub s w) hL_nn))
          (stdNormalPDF_nonneg s)
      _ = L * (stdNormalPDF s * |s|) + L * |w| * stdNormalPDF s := by ring
  have hibp_Iic : ∀ w : ℝ,
      (∫ s in Set.Iic w, stdNormalCDF s * deriv h s) =
        ∫ s in Set.Iic w, stdNormalPDF s * (h w - h s) := by
    intro w
    have hint1 : IntegrableOn (fun s ↦ stdNormalCDF s * deriv h s) (Set.Iic w) volume := by
      refine ((integrableOn_Iic_stdNormalCDF w).mul_const L).mono'
        (continuous_stdNormalCDF.aestronglyMeasurable.mul hmeas_dh).restrict
        (ae_of_all _ fun s ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalCDF_nonneg s)]
      exact mul_le_mul_of_nonneg_left (hL s) (stdNormalCDF_nonneg s)
    have hint2 : IntegrableOn (fun s ↦ stdNormalPDF s * (h s - h w)) (Set.Iic w) volume :=
      (hint_pdf_sub w).integrableOn
    have hlim_int := intervalIntegral_tendsto_integral_Iic w (hint2.add hint1) tendsto_id
    have hlim_bnd : Tendsto (fun a : ℝ ↦ -stdNormalCDF a * (h a - h w)) atBot (𝓝 0) := by
      have ht0 := (tendsto_pow_mul_one_sub_stdNormalCDF_atTop 0).comp tendsto_neg_atBot_atTop
      have ht1 := (tendsto_pow_mul_one_sub_stdNormalCDF_atTop 1).comp tendsto_neg_atBot_atTop
      have hdom : Tendsto (fun a : ℝ ↦ L * ((-a) ^ 1 * (1 - stdNormalCDF (-a))) +
          (L * |w|) * ((-a) ^ 0 * (1 - stdNormalCDF (-a)))) atBot (𝓝 0) := by
        simpa using (ht1.const_mul L).add (ht0.const_mul (L * |w|))
      refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
        (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hdom)
      filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with a ha
      have hd := hlip_h.dist_le_mul a w
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL_nn] at hd
      have hcdf_eq : stdNormalCDF a = 1 - stdNormalCDF (-a) := by
        have := stdNormalCDF_neg (-a); rw [neg_neg] at this; exact this
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (stdNormalCDF_nonneg a), hcdf_eq]
      have habs : |a - w| ≤ -a + |w| := (abs_sub a w).trans (by rw [abs_of_nonpos ha])
      have hnn : 0 ≤ 1 - stdNormalCDF (-a) := sub_nonneg.mpr (stdNormalCDF_le_one (-a))
      simp only [pow_one, pow_zero, one_mul]
      calc (1 - stdNormalCDF (-a)) * |h a - h w|
        _ ≤ (1 - stdNormalCDF (-a)) * (L * (-a + |w|)) :=
          mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left habs hL_nn)) hnn
        _ = L * (-a * (1 - stdNormalCDF (-a))) + L * |w| * (1 - stdNormalCDF (-a)) := by ring
    have hstep : ∀ a : ℝ,
        (∫ s in a..w, (stdNormalPDF s * (h s - h w) + stdNormalCDF s * deriv h s)) =
          -stdNormalCDF a * (h a - h w) := fun a ↦ by
      have hd_cdf : deriv stdNormalCDF = stdNormalPDF :=
        funext fun u ↦ (hasDerivAt_stdNormalCDF u).deriv
      have hac_cdf : AbsolutelyContinuousOnInterval stdNormalCDF a w :=
        (contDiff_one_iff_deriv.mpr ⟨fun u ↦ (hasDerivAt_stdNormalCDF u).differentiableAt,
          by rw [hd_cdf]; exact continuous_stdNormalPDF⟩).contDiffOn
          |>.absolutelyContinuousOnInterval
      have hac_hw : AbsolutelyContinuousOnInterval (fun u ↦ h u - h w) a w :=
        (hac a w).sub (LipschitzWith.const (h w)).lipschitzOnWith.absolutelyContinuousOnInterval
      have hibp := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hac_cdf hac_hw
      have hcongr : (∫ s in a..w, (stdNormalPDF s * (h s - h w) + stdNormalCDF s * deriv h s)) =
          ∫ s in a..w, (deriv stdNormalCDF s * (h s - h w) +
            stdNormalCDF s * deriv (fun u ↦ h u - h w) s) :=
        intervalIntegral.integral_congr fun s _ ↦ by rw [hd_cdf, deriv_sub_const]
      rw [hcongr, hibp, sub_self, mul_zero, zero_sub, neg_mul]
    have hzero := tendsto_nhds_unique hlim_int (by simpa [funext hstep] using hlim_bnd)
    dsimp only [Pi.add_apply] at hzero
    rw [integral_add hint2 hint1] at hzero
    have hneg : (∫ s in Set.Iic w, stdNormalPDF s * (h w - h s)) =
        -∫ s in Set.Iic w, stdNormalPDF s * (h s - h w) := by
      rw [← integral_neg]; exact setIntegral_congr_fun measurableSet_Iic fun _ _ ↦ by ring
    linarith
  have hibp_Ioi : ∀ w : ℝ,
      (∫ s in Set.Ioi w, (1 - stdNormalCDF s) * deriv h s) =
        ∫ s in Set.Ioi w, stdNormalPDF s * (h s - h w) := by
    intro w
    have hint1 : IntegrableOn (fun s ↦ (1 - stdNormalCDF s) * deriv h s) (Set.Ioi w) volume := by
      refine ((integrableOn_Ioi_one_sub_stdNormalCDF w).mul_const L).mono'
        ((continuous_const.sub continuous_stdNormalCDF).aestronglyMeasurable.mul hmeas_dh).restrict
        (ae_of_all _ fun s ↦ ?_)
      have hnn := sub_nonneg.mpr (stdNormalCDF_le_one s)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hL s) hnn
    have hint2 : IntegrableOn (fun s ↦ stdNormalPDF s * (h s - h w)) (Set.Ioi w) volume :=
      (hint_pdf_sub w).integrableOn
    have hlim_int := intervalIntegral_tendsto_integral_Ioi w (hint2.sub hint1) tendsto_id
    have hlim_bnd : Tendsto (fun b : ℝ ↦ -(1 - stdNormalCDF b) * (h b - h w)) atTop (𝓝 0) := by
      have hdom : Tendsto (fun b : ℝ ↦ L * (b ^ 1 * (1 - stdNormalCDF b)) +
          (L * |w|) * (b ^ 0 * (1 - stdNormalCDF b))) atTop (𝓝 0) := by
        simpa using ((tendsto_pow_mul_one_sub_stdNormalCDF_atTop 1).const_mul L).add
          ((tendsto_pow_mul_one_sub_stdNormalCDF_atTop 0).const_mul (L * |w|))
      refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
        (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hdom)
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with b hb
      have hd := hlip_h.dist_le_mul b w
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL_nn] at hd
      have hnn := sub_nonneg.mpr (stdNormalCDF_le_one b)
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hnn]
      have habs : |b - w| ≤ b + |w| := (abs_sub b w).trans (by rw [abs_of_nonneg hb])
      simp only [pow_one, pow_zero, one_mul]
      calc (1 - stdNormalCDF b) * |h b - h w|
        _ ≤ (1 - stdNormalCDF b) * (L * (b + |w|)) :=
          mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left habs hL_nn)) hnn
        _ = L * (b * (1 - stdNormalCDF b)) + L * |w| * (1 - stdNormalCDF b) := by ring
    have hstep : ∀ b : ℝ,
        (∫ s in w..b, (stdNormalPDF s * (h s - h w) - (1 - stdNormalCDF s) * deriv h s)) =
          -(1 - stdNormalCDF b) * (h b - h w) := fun b ↦ by
      have hd_q : deriv (fun u ↦ -(1 - stdNormalCDF u)) = stdNormalPDF :=
        funext fun u ↦ by
          convert ((hasDerivAt_stdNormalCDF u).const_sub 1).fun_neg.deriv using 1; ring
      have hac_q : AbsolutelyContinuousOnInterval (fun s ↦ -(1 - stdNormalCDF s)) w b :=
        (contDiff_one_iff_deriv.mpr
          ⟨fun u ↦ ((hasDerivAt_stdNormalCDF u).const_sub 1).fun_neg.differentiableAt,
            by rw [hd_q]; exact continuous_stdNormalPDF⟩).contDiffOn
          |>.absolutelyContinuousOnInterval
      have hac_hw : AbsolutelyContinuousOnInterval (fun u ↦ h u - h w) w b :=
        (hac w b).sub (LipschitzWith.const (h w)).lipschitzOnWith.absolutelyContinuousOnInterval
      have hibp := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hac_q hac_hw
      have hcongr :
          (∫ s in w..b, (stdNormalPDF s * (h s - h w) - (1 - stdNormalCDF s) * deriv h s)) =
            ∫ s in w..b, (deriv (fun u ↦ -(1 - stdNormalCDF u)) s * (h s - h w) +
              (-(1 - stdNormalCDF s)) * deriv (fun u ↦ h u - h w) s) :=
        intervalIntegral.integral_congr fun s _ ↦ by rw [congr_fun hd_q s, deriv_sub_const]; ring
      rw [hcongr, hibp, sub_self, mul_zero, sub_zero]
    have hzero := tendsto_nhds_unique hlim_int (by simpa [funext hstep] using hlim_bnd)
    dsimp only [Pi.sub_apply] at hzero
    rw [integral_sub hint2 hint1] at hzero; linarith
  set c := stdNormalExpect h
  have hp1 : Integrable (fun s ↦ stdNormalPDF s * h s) volume :=
    integrable_stdNormalLaw_iff.mp hh_int
  have hc_smul : c = ∫ s, stdNormalPDF s * h s :=
    stdNormalExpect_eq_integral_mul_pdf h
  have hsub_c : ∀ w : ℝ, h w - c =
      (∫ s in Set.Iic w, stdNormalCDF s * deriv h s) -
        (∫ s in Set.Ioi w, (1 - stdNormalCDF s) * deriv h s) := by
    intro w
    rw [hibp_Iic w, hibp_Ioi w]
    have htot := integral_add_compl (s := Set.Iic w) measurableSet_Iic (hint_pdf_sub w)
    rw [compl_Iic] at htot
    have hp2 := (integrable_gaussianPDFReal 0 1).mul_const (h w)
    have htot_val : (∫ s, stdNormalPDF s * (h s - h w)) = c - h w := by
      have heq : (fun s ↦ stdNormalPDF s * (h s - h w)) =
          fun s ↦ stdNormalPDF s * h s - stdNormalPDF s * h w := by ext s; ring
      rw [heq, integral_sub hp1 hp2, integral_mul_const,
        integral_gaussianPDFReal_eq_one 0 one_ne_zero, one_mul, ← hc_smul]
    have hneg : (∫ s in Set.Iic w, stdNormalPDF s * (h w - h s)) =
        -∫ s in Set.Iic w, stdNormalPDF s * (h s - h w) := by
      rw [← integral_neg]; exact setIntegral_congr_fun measurableSet_Iic fun _ _ ↦ by ring
    linarith
  have hsol_green : ∀ w : ℝ, normalSteinSol h w =
      -((1 - stdNormalCDF w) / stdNormalPDF w) * (∫ s in Set.Iic w, stdNormalCDF s * deriv h s) -
        (stdNormalCDF w / stdNormalPDF w) *
          (∫ s in Set.Ioi w, (1 - stdNormalCDF s) * deriv h s) := by
    intro w
    have hp_ne := (stdNormalPDF_pos w).ne'
    rw [hibp_Iic w, hibp_Ioi w]
    have hp_const := (integrable_gaussianPDFReal 0 1).mul_const (h w)
    have hIic_split : (∫ s in Set.Iic w, stdNormalPDF s * (h w - h s)) =
        h w * stdNormalCDF w - ∫ s in Set.Iic w, stdNormalPDF s * h s := by
      have heq : (fun s ↦ stdNormalPDF s * (h w - h s)) =
          fun s ↦ stdNormalPDF s * h w - stdNormalPDF s * h s := by ext s; ring
      rw [heq, integral_sub hp_const.integrableOn hp1.integrableOn, integral_mul_const,
        ← stdNormalCDF_eq_integral_Iic w]; ring
    have hIoi_split : (∫ s in Set.Ioi w, stdNormalPDF s * (h s - h w)) =
        (∫ s in Set.Ioi w, stdNormalPDF s * h s) - h w * (1 - stdNormalCDF w) := by
      have heq : (fun s ↦ stdNormalPDF s * (h s - h w)) =
          fun s ↦ stdNormalPDF s * h s - stdNormalPDF s * h w := by ext s; ring
      rw [heq, integral_sub hp1.integrableOn hp_const.integrableOn, integral_mul_const,
        ← one_sub_stdNormalCDF_eq_integral_Ioi w]; ring
    have htot_h : (∫ s in Set.Iic w, stdNormalPDF s * h s) +
        (∫ s in Set.Ioi w, stdNormalPDF s * h s) = c := by
      have ht := integral_add_compl (s := Set.Iic w) measurableSet_Iic hp1
      rw [compl_Iic, ← hc_smul] at ht; exact ht
    have hsol_pdf : stdNormalPDF w * normalSteinSol h w =
        -(stdNormalCDF w * c - ∫ s in Set.Iic w, stdNormalPDF s * h s) := by
      rw [normalSteinSol_eq_neg_integral_Iic hh_int w]
      have hpt : (∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) =
          Real.sqrt (2 * Real.pi) *
            (stdNormalCDF w * c - ∫ s in Set.Iic w, stdNormalPDF s * h s) := by
        simp_rw [exp_neg_half_sq_eq_sqrt_two_pi_mul_pdf]
        have heq : (fun t ↦ Real.sqrt (2 * Real.pi) * stdNormalPDF t *
              (stdNormalExpect h - h t)) =
            fun t ↦ Real.sqrt (2 * Real.pi) * (stdNormalPDF t * c - stdNormalPDF t * h t) := by
          ext t; simp only [c]; ring
        rw [heq, integral_const_mul, integral_sub
          ((integrable_gaussianPDFReal 0 1).integrableOn.mul_const c) hp1.integrableOn,
          integral_mul_const, ← stdNormalCDF_eq_integral_Iic w]
      have hpref : stdNormalPDF w * (-Real.exp (w ^ 2 / 2) * Real.sqrt (2 * Real.pi)) = -1 := by
        calc stdNormalPDF w * (-Real.exp (w ^ 2 / 2) * Real.sqrt (2 * Real.pi))
          _ = -(Real.exp (w ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * stdNormalPDF w)) := by ring
          _ = -(Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2)) := by
              rw [← exp_neg_half_sq_eq_sqrt_two_pi_mul_pdf]
          _ = -1 := by rw [exp_half_sq_mul_neg]
      rw [hpt]
      set X := stdNormalCDF w * c - ∫ s in Set.Iic w, stdNormalPDF s * h s
      calc stdNormalPDF w * (-Real.exp (w ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * X))
        _ = (stdNormalPDF w * (-Real.exp (w ^ 2 / 2) * Real.sqrt (2 * Real.pi))) * X := by ring
        _ = -1 * X := by rw [hpref]
        _ = -X := by ring
    rw [hIic_split, hIoi_split]
    apply mul_left_cancel₀ hp_ne
    rw [hsol_pdf, ← htot_h]; field_simp; ring
  have hbound_Iic : ∀ w : ℝ, |∫ s in Set.Iic w, stdNormalCDF s * deriv h s| ≤
      (stdNormalPDF w + w * stdNormalCDF w) * L := fun w ↦ by
    rw [← Real.norm_eq_abs, ← integral_Iic_cdf_eq w, ← integral_mul_const]
    refine norm_integral_le_of_norm_le ((integrableOn_Iic_stdNormalCDF w).mul_const L)
      (ae_of_all _ fun s ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalCDF_nonneg s)]
    exact mul_le_mul_of_nonneg_left (hL s) (stdNormalCDF_nonneg s)
  have hbound_Ioi : ∀ w : ℝ, |∫ s in Set.Ioi w, (1 - stdNormalCDF s) * deriv h s| ≤
      (stdNormalPDF w - w * (1 - stdNormalCDF w)) * L := fun w ↦ by
    rw [← Real.norm_eq_abs, ← integral_Ioi_one_sub_cdf_eq w, ← integral_mul_const]
    refine norm_integral_le_of_norm_le ((integrableOn_Ioi_one_sub_stdNormalCDF w).mul_const L)
      (ae_of_all _ fun s ↦ ?_)
    have hnn := sub_nonneg.mpr (stdNormalCDF_le_one s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hL s) hnn
  have h_sup : ∀ w : ℝ, |normalSteinSol h w| ≤ 2 * L := fun w ↦ by
    have hp_pos := stdNormalPDF_pos w
    have hp_ne := hp_pos.ne'
    have hcb := (abs_comb_le (div_nonneg (sub_nonneg.mpr (stdNormalCDF_le_one w)) hp_pos.le)
      (div_nonneg (stdNormalCDF_nonneg w) hp_pos.le) (hbound_Iic w) (hbound_Ioi w)).2
    rw [hsol_green w]
    have halg : ((1 - stdNormalCDF w) / stdNormalPDF w) *
          ((stdNormalPDF w + w * stdNormalCDF w) * L) +
        (stdNormalCDF w / stdNormalPDF w) *
          ((stdNormalPDF w - w * (1 - stdNormalCDF w)) * L) = L := by field_simp; ring
    linarith
  have h_deriv_sup : ∀ w : ℝ, |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi) * L := by
    intro w
    have hp_pos := stdNormalPDF_pos w
    have hp_ne := hp_pos.ne'
    have hdeq : deriv (normalSteinSol h) w =
        ((stdNormalPDF w - w * (1 - stdNormalCDF w)) / stdNormalPDF w) *
          (∫ s in Set.Iic w, stdNormalCDF s * deriv h s) -
        ((stdNormalPDF w + w * stdNormalCDF w) / stdNormalPDF w) *
          (∫ s in Set.Ioi w, (1 - stdNormalCDF s) * deriv h s) := by
      rw [hderiv_eq w, hsol_green w, hsub_c w]; field_simp; ring
    rw [hdeq]
    have hB_nn : 0 ≤ stdNormalPDF w - w * (1 - stdNormalCDF w) := steinKernelB_nonneg w
    have hA_nn : 0 ≤ stdNormalPDF w + w * stdNormalCDF w := steinKernelA_nonneg w
    have hcb := (abs_comb_le (div_nonneg hB_nn hp_pos.le)
      (div_nonneg hA_nn hp_pos.le) (hbound_Iic w) (hbound_Ioi w)).1
    have halg : ((stdNormalPDF w - w * (1 - stdNormalCDF w)) / stdNormalPDF w) *
          ((stdNormalPDF w + w * stdNormalCDF w) * L) +
        ((stdNormalPDF w + w * stdNormalCDF w) / stdNormalPDF w) *
          ((stdNormalPDF w - w * (1 - stdNormalCDF w)) * L) =
        (2 * (stdNormalPDF w + w * stdNormalCDF w) *
          (stdNormalPDF w - w * (1 - stdNormalCDF w)) / stdNormalPDF w) * L := by field_simp; ring
    linarith [mul_le_mul_of_nonneg_right (two_mul_steinKernelA_mul_steinKernelB_div_le w) hL_nn]
  have hlip_df : LipschitzWith (Real.toNNReal (2 * L)) (deriv (normalSteinSol h)) := by
    set g0 : ℝ → ℝ := fun w ↦ w * normalSteinSol h w
    have hg0_deriv : ∀ w : ℝ,
        HasDerivAt g0 ((1 + w ^ 2) * normalSteinSol h w + w * (h w - c)) w := fun w ↦
      ((hasDerivAt_id w).fun_mul
        (hasDerivAt_normalSteinSol hh_int hcont_h.continuousAt)).congr_deriv
        (by simp only [id_eq]; ring)
    have hlip_g0 : LipschitzWith (Real.toNNReal L) g0 := by
      refine lipschitzWith_of_nnnorm_deriv_le (fun w ↦ (hg0_deriv w).differentiableAt) fun w ↦ ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal L hL_nn,
        (hg0_deriv w).deriv, Real.norm_eq_abs]
      have hp_pos := stdNormalPDF_pos w
      have hp_ne := hp_pos.ne'
      set A := (1 + w ^ 2) * (1 - stdNormalCDF w) - w * stdNormalPDF w
      set Bw := (1 + w ^ 2) * stdNormalCDF w + w * stdNormalPDF w
      have hge_eq : (1 + w ^ 2) * normalSteinSol h w + w * (h w - c) =
          -(A / stdNormalPDF w) * (∫ s in Set.Iic w, stdNormalCDF s * deriv h s) -
            (Bw / stdNormalPDF w) * (∫ s in Set.Ioi w, (1 - stdNormalCDF s) * deriv h s) := by
        rw [hsol_green w, hsub_c w]; simp only [A, Bw]; field_simp; ring
      rw [hge_eq]
      have hcb := (abs_comb_le (div_nonneg (one_add_sq_mul_one_sub_stdNormalCDF_sub_nonneg w)
        hp_pos.le) (div_nonneg (one_add_sq_mul_stdNormalCDF_add_nonneg w) hp_pos.le)
        (hbound_Iic w) (hbound_Ioi w)).2
      have halg : (A / stdNormalPDF w) * ((stdNormalPDF w + w * stdNormalCDF w) * L) +
          (Bw / stdNormalPDF w) * ((stdNormalPDF w - w * (1 - stdNormalCDF w)) * L) = L := by
        simp only [A, Bw]; field_simp; ring
      linarith
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.coe_toNNReal (2 * L) (by positivity), Real.dist_eq, Real.dist_eq,
      hderiv_eq x, hderiv_eq y]
    have hd1 := hlip_g0.dist_le_mul x y
    have hd2 := hlip_h.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL_nn] at hd1 hd2
    have hsplit : g0 x + (h x - c) - (g0 y + (h y - c)) = (g0 x - g0 y) + (h x - h y) := by ring
    rw [hsplit]
    linarith [abs_add_le (g0 x - g0 y) (h x - h y)]
  refine ⟨h_sup, h_deriv_sup, fun w ↦ ?_⟩
  simpa [Real.norm_eq_abs, Real.coe_toNNReal (2 * L) (by positivity)] using
    norm_deriv_le_of_lipschitz (x₀ := w) hlip_df

/-- Uniform supremum bound $|f_h(w)| \le 2 L$ for locally absolutely continuous `h` with
$|h'(t)| \le L$ (Lemma 2.5(2) `\label{lem31}` `\label{i32}`, `SteinIntro.tex:690-694`). -/
theorem abs_normalSteinSol_le_of_lipschitzDeriv {h : ℝ → ℝ} {L : ℝ}
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hL : ∀ t : ℝ, |deriv h t| ≤ L) (w : ℝ) :
    |normalSteinSol h w| ≤ 2 * L :=
  (normalSteinSol_ac_estimates hac hL).1 w

/-- Sharp first-derivative bound $|f_h'(w)| \le \sqrt{2/\pi}\,L$ for locally absolutely continuous
`h` with $|h'(t)| \le L$ (Lemma 2.5(2) `\label{lem31}` `\label{i32}`,
`SteinIntro.tex:690-694`). -/
theorem abs_deriv_normalSteinSol_le_of_lipschitzDeriv {h : ℝ → ℝ} {L : ℝ}
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hL : ∀ t : ℝ, |deriv h t| ≤ L) (w : ℝ) :
    |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi) * L :=
  (normalSteinSol_ac_estimates hac hL).2.1 w

/-- Uniform second-derivative bound $|f_h''(w)| \le 2 L$ for locally absolutely continuous `h`
with $|h'(t)| \le L$ (Lemma 2.5(2) `\label{lem31}` `\label{i32}`, `SteinIntro.tex:690-694`). -/
theorem abs_iteratedDeriv_two_normalSteinSol_le_of_lipschitzDeriv {h : ℝ → ℝ} {L : ℝ}
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hL : ∀ t : ℝ, |deriv h t| ≤ L) (w : ℝ) :
    |deriv (deriv (normalSteinSol h)) w| ≤ 2 * L :=
  (normalSteinSol_ac_estimates hac hL).2.2 w

/-! ### Section 4: Bounded Continuous Stein Solution Helper (`Lem2_1_2`) -/

/-- Every bounded continuous test function `h : ℝ → ℝ` admits a locally absolutely continuous
solution `f` of the normal Stein equation `normalSteinOp f w = h w - stdNormalExpect h` with
`stdNormalLaw`-integrable derivative (converse helper for Lemma 2.1(2) `\label{lem1}`,
`SteinIntro.tex:569-572`, `637-644`). -/
theorem exists_ac_normalSteinSol_of_continuous_bounded {h : ℝ → ℝ}
    (hCont : Continuous h) (hBdd : ∃ B : ℝ, ∀ t : ℝ, |h t| ≤ B) :
    ∃ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) ∧
      Integrable (deriv f) stdNormalLaw ∧
      ∀ w : ℝ, normalSteinOp f w = h w - stdNormalExpect h := by
  obtain ⟨B, hB⟩ := hBdd
  have hInt : Integrable h stdNormalLaw :=
    Integrable.of_bound hCont.aestronglyMeasurable B
      (ae_of_all _ fun t ↦ by simpa [Real.norm_eq_abs] using hB t)
  refine ⟨normalSteinSol h, locallyAC_normalSteinSol hInt, ?_, ?_⟩
  · have hderiv_eq : deriv (normalSteinSol h) =
        fun w ↦ w * normalSteinSol h w + h w - stdNormalExpect h :=
      funext fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hInt hCont w).deriv
    have hcont_df : Continuous (deriv (normalSteinSol h)) := by
      rw [hderiv_eq]
      exact ((continuous_id.mul (continuous_normalSteinSol hInt)).add hCont).sub continuous_const
    have hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ B + |stdNormalExpect h| := fun t ↦ by
      linarith [abs_sub (h t) (stdNormalExpect h), hB t]
    refine Integrable.of_bound hcont_df.aestronglyMeasurable (2 * (B + |stdNormalExpect h|))
      (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs]
    exact abs_deriv_normalSteinSol_le_of_bounded hCont.measurable hM w
  · intro w
    unfold normalSteinOp
    rw [(hasDerivAt_normalSteinSol_of_continuous hInt hCont w).deriv]
    ring

end SteinMethod
