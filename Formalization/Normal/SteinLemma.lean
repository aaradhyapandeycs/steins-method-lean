/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.NormalStein
import Formalization.Normal.SolutionBounds
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Stein's Characterizing Lemma for the Standard Normal Law (`Formalization.Normal.SteinLemma`)

Proves Lemma 2.1 (`\label{lem1}`, `SteinIntro.tex:562-574`, proof at `SteinIntro.tex:628-645`) of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `integrable_mul_and_integral_eq_deriv_stdNormal` and
  `integrable_mul_of_integrable_deriv_stdNormal`: the Tonelli/Fubini half-line integration-by-parts
  argument (`SteinIntro.tex:628-636`) establishing integrability of $Z f(Z)$ and
  $\mathbb{E}[Z f(Z)] = \mathbb{E}[f'(Z)]$ for $Z \sim \mathcal{N}(0, 1)$.
* `integrable_normalSteinOp_of_map_eq` and `integral_normalSteinOp_eq_zero_of_map_eq`:
  **Lemma 2.1(1)** (`\label{lem1}` item 1, `SteinIntro.tex:562-569`).
* `map_eq_stdNormalLaw_of_integral_normalSteinOp_eq_zero`:
  **Lemma 2.1(2)** (`\label{lem1}` item 2, `SteinIntro.tex:570-574`; ruling `D5` literal), proved
  without moment hypotheses via bounded continuous ramp approximations to cumulative distribution
  indicators together with `exists_ac_normalSteinSol_of_continuous_bounded`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

section DensityHelpers

private lemma steinLemma_continuous_of_ac {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  have hcont : ContinuousOn f (uIcc (x - 1) (x + 1)) := (hf (x - 1) (x + 1)).continuousOn
  have hle : x - 1 ≤ x + 1 := by linarith
  rw [uIcc_of_le hle] at hcont
  exact hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

private lemma steinLemma_integrable_stdNormal_iff {g : ℝ → ℝ} :
    Integrable g (gaussianReal 0 1) ↔
      Integrable (fun w ↦ g w * gaussianPDFReal 0 1 w) volume := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF]

private lemma steinLemma_integral_stdNormal_eq {g : ℝ → ℝ} :
    ∫ w, g w ∂gaussianReal 0 1 = ∫ w, g w * gaussianPDFReal 0 1 w := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, mul_comm]

private lemma steinLemma_integrable_mul_pdf :
    Integrable (fun w ↦ w * gaussianPDFReal 0 1 w) volume := by
  have hid : Integrable (fun w : ℝ ↦ w) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := 1) 1)
  exact steinLemma_integrable_stdNormal_iff.mp hid

private lemma steinLemma_integral_mul_pdf :
    ∫ w, w * gaussianPDFReal 0 1 w = 0 := by
  rw [← steinLemma_integral_stdNormal_eq]
  exact integral_id_gaussianReal

private lemma steinLemma_hasDerivAt_neg_pdf (w : ℝ) :
    HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x) (w * gaussianPDFReal 0 1 w) w := by
  have h_inner : HasDerivAt (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) (-w) w := by
    have h0 : (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) = fun x : ℝ ↦ -(x ^ 2) / 2 := by
      ext x
      simp
    rw [h0]
    convert (((hasDerivAt_id' w).fun_pow 2).neg.div_const (2 : ℝ)) using 1
    ring
  have h_exp : HasDerivAt
      (fun x : ℝ ↦ Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0))))
      (Real.exp (-(w - 0) ^ 2 / (2 * (1 : ℝ≥0))) * (-w)) w :=
    h_inner.exp
  have h_pdf : HasDerivAt (gaussianPDFReal 0 1) (-w * gaussianPDFReal 0 1 w) w := by
    rw [gaussianPDFReal_def]
    convert h_exp.const_mul (√(2 * Real.pi * (1 : ℝ≥0)))⁻¹ using 1
    ring
  convert h_pdf.neg using 1
  ring

private lemma steinLemma_tendsto_neg_pdf_of_sq {l : Filter ℝ}
    (hsq : Tendsto (fun x : ℝ ↦ x ^ 2) l atTop) :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x) l (𝓝 0) := by
  have hdiv : Tendsto (fun x : ℝ ↦ x ^ 2 / 2) l atTop :=
    hsq.atTop_div_const (by norm_num)
  have hneg : Tendsto (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) l atBot := by
    have h' : Tendsto (fun x : ℝ ↦ -(x ^ 2 / 2)) l atBot :=
      tendsto_neg_atTop_atBot.comp hdiv
    refine h'.congr fun x ↦ ?_
    simp [neg_div]
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0)))) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hpdf : Tendsto (gaussianPDFReal 0 1) l (𝓝 0) := by
    rw [gaussianPDFReal_def]
    simpa using hexp.const_mul (√(2 * Real.pi * (1 : ℝ≥0)))⁻¹
  simpa using hpdf.neg

private lemma steinLemma_tendsto_neg_pdf_atTop :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x) atTop (𝓝 0) :=
  steinLemma_tendsto_neg_pdf_of_sq (tendsto_pow_atTop (by norm_num))

private lemma steinLemma_tendsto_neg_pdf_atBot :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x) atBot (𝓝 0) := by
  refine steinLemma_tendsto_neg_pdf_of_sq ?_
  have h : Tendsto (fun x : ℝ ↦ (-x) ^ 2) atBot atTop :=
    (tendsto_pow_atTop (by norm_num)).comp tendsto_neg_atBot_atTop
  simpa using h

private lemma steinLemma_integral_Ioi_mul_pdf (t : ℝ) :
    ∫ w in Ioi t, w * gaussianPDFReal 0 1 w = gaussianPDFReal 0 1 t := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := t)
    (fun w _ ↦ steinLemma_hasDerivAt_neg_pdf w)
    steinLemma_integrable_mul_pdf.integrableOn
    steinLemma_tendsto_neg_pdf_atTop
  simpa using h

private lemma steinLemma_integral_Iic_mul_pdf (t : ℝ) :
    ∫ w in Iic t, w * gaussianPDFReal 0 1 w = -gaussianPDFReal 0 1 t := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := t)
    (fun w _ ↦ steinLemma_hasDerivAt_neg_pdf w)
    steinLemma_integrable_mul_pdf.integrableOn
    steinLemma_tendsto_neg_pdf_atBot
  simpa using h

private lemma steinLemma_integral_Iio_mul_pdf (t : ℝ) :
    ∫ w in Iio t, w * gaussianPDFReal 0 1 w = -gaussianPDFReal 0 1 t := by
  rw [setIntegral_congr_set Iio_ae_eq_Iic, steinLemma_integral_Iic_mul_pdf]

end DensityHelpers

section HalfLineFubini

private lemma steinLemma_integrableOn_and_integral_Ioi_pdf {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun t ↦ deriv f t * gaussianPDFReal 0 1 t) volume) :
    IntegrableOn (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) (Ioi 0) volume ∧
      ∫ w in Ioi 0, w * (f w - f 0) * gaussianPDFReal 0 1 w =
        ∫ t in Ioi 0, deriv f t * gaussianPDFReal 0 1 t := by
  let S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1}
  let K : ℝ × ℝ → ℝ :=
    S.indicator fun p ↦ deriv f p.2 * (p.1 * gaussianPDFReal 0 1 p.1)
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hK_meas : Measurable K := by
    refine Measurable.indicator ?_ hS_meas
    exact ((measurable_deriv f).comp measurable_snd).mul
      (measurable_fst.mul ((measurable_gaussianPDFReal 0 1).comp measurable_fst))
  have hK_int : Integrable K (volume.prod volume) := by
    rw [integrable_prod_iff' hK_meas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
    · by_cases ht : 0 < t
      · have h_ind : (fun w ↦ K (w, t)) =
            (Ioi t).indicator (fun w ↦ deriv f t * (w * gaussianPDFReal 0 1 w)) := by
          ext w
          by_cases htw : t < w <;> simp [K, S, ht, htw]
        rw [h_ind]
        exact (steinLemma_integrable_mul_pdf.const_mul (deriv f t)).indicator measurableSet_Ioi
      · have h_zero : (fun w ↦ K (w, t)) = 0 := by
          ext w
          simp [K, S, ht]
        rw [h_zero]
        exact integrable_zero _ _ _
    · have h_norm_eq : (fun t ↦ ∫ w, ‖K (w, t)‖) =
          (Ioi (0 : ℝ)).indicator (fun t ↦ |deriv f t| * gaussianPDFReal 0 1 t) := by
        ext t
        by_cases ht : 0 < t
        · have ht_mem : t ∈ Ioi (0 : ℝ) := ht
          have h_slice : (fun w ↦ ‖K (w, t)‖) =
              (Ioi t).indicator (fun w ↦ |deriv f t| * (w * gaussianPDFReal 0 1 w)) := by
            ext w
            by_cases htw : t < w
            · have hw0 : 0 ≤ w := le_of_lt (ht.trans htw)
              have hφ0 : 0 ≤ gaussianPDFReal 0 1 w := gaussianPDFReal_nonneg 0 1 w
              simp [K, S, ht, htw, abs_of_nonneg hw0, abs_of_nonneg hφ0]
            · simp [K, S, ht, htw]
          rw [h_slice, integral_indicator measurableSet_Ioi, integral_const_mul,
            steinLemma_integral_Ioi_mul_pdf, indicator_of_mem ht_mem]
        · have ht_not : t ∉ Ioi (0 : ℝ) := ht
          have h_zero : (fun w ↦ ‖K (w, t)‖) = 0 := by
            ext w
            simp [K, S, ht]
          rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem ht_not]
      rw [h_norm_eq]
      have h_abs : (fun t ↦ |deriv f t| * gaussianPDFReal 0 1 t) =
          fun t ↦ ‖deriv f t * gaussianPDFReal 0 1 t‖ := by
        ext t
        simp [abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
      rw [h_abs]
      exact hf'.norm.indicator measurableSet_Ioi
  have h_left : (fun w ↦ ∫ t, K (w, t)) =
      (Ioi (0 : ℝ)).indicator (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) := by
    ext w
    by_cases hw : 0 < w
    · have hw_mem : w ∈ Ioi (0 : ℝ) := hw
      have h_slice : (fun t ↦ K (w, t)) =
          (Ioo 0 w).indicator (fun t ↦ deriv f t * (w * gaussianPDFReal 0 1 w)) := by
        ext t
        by_cases ht : 0 < t ∧ t < w <;> simp [K, S, ht]
      rw [h_slice, integral_indicator measurableSet_Ioo, integral_mul_const,
        setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hw.le,
        (hf 0 w).integral_deriv_eq_sub, indicator_of_mem hw_mem]
      ring
    · have hw_not : w ∉ Ioi (0 : ℝ) := hw
      have h_zero : (fun t ↦ K (w, t)) = 0 := by
        ext t
        have hnot : ¬ (0 < t ∧ t < w) := fun h ↦ hw (h.1.trans h.2)
        simp [K, S, hnot]
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem hw_not]
  have h_right : (fun t ↦ ∫ w, K (w, t)) =
      (Ioi (0 : ℝ)).indicator (fun t ↦ deriv f t * gaussianPDFReal 0 1 t) := by
    ext t
    by_cases ht : 0 < t
    · have ht_mem : t ∈ Ioi (0 : ℝ) := ht
      have h_slice : (fun w ↦ K (w, t)) =
          (Ioi t).indicator (fun w ↦ deriv f t * (w * gaussianPDFReal 0 1 w)) := by
        ext w
        by_cases htw : t < w <;> simp [K, S, ht, htw]
      rw [h_slice, integral_indicator measurableSet_Ioi, integral_const_mul,
        steinLemma_integral_Ioi_mul_pdf, indicator_of_mem ht_mem]
    · have ht_not : t ∉ Ioi (0 : ℝ) := ht
      have h_zero : (fun w ↦ K (w, t)) = 0 := by
        ext w
        simp [K, S, ht]
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem ht_not]
  have h_int_left :
      IntegrableOn (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) (Ioi 0) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mp (h_left ▸ hK_int.integral_prod_left)
  refine ⟨h_int_left, ?_⟩
  have h_fub := (integral_prod K hK_int).symm.trans (integral_prod_symm K hK_int)
  rw [h_left, integral_indicator measurableSet_Ioi, h_right,
    integral_indicator measurableSet_Ioi] at h_fub
  exact h_fub

private lemma steinLemma_integrableOn_and_integral_Iic_pdf {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun t ↦ deriv f t * gaussianPDFReal 0 1 t) volume) :
    IntegrableOn (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) (Iic 0) volume ∧
      ∫ w in Iic 0, w * (f w - f 0) * gaussianPDFReal 0 1 w =
        ∫ t in Iic 0, deriv f t * gaussianPDFReal 0 1 t := by
  let S : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ p.2 ≤ 0}
  let K : ℝ × ℝ → ℝ :=
    S.indicator fun p ↦ -deriv f p.2 * (p.1 * gaussianPDFReal 0 1 p.1)
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hK_meas : Measurable K := by
    refine Measurable.indicator ?_ hS_meas
    exact (((measurable_deriv f).comp measurable_snd).neg).mul
      (measurable_fst.mul ((measurable_gaussianPDFReal 0 1).comp measurable_fst))
  have hK_int : Integrable K (volume.prod volume) := by
    rw [integrable_prod_iff' hK_meas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
    · by_cases ht : t ≤ 0
      · have h_ind : (fun w ↦ K (w, t)) =
            (Iio t).indicator (fun w ↦ -deriv f t * (w * gaussianPDFReal 0 1 w)) := by
          ext w
          by_cases hwt : w < t <;> simp [K, S, ht, hwt]
        rw [h_ind]
        exact (steinLemma_integrable_mul_pdf.const_mul (-deriv f t)).indicator measurableSet_Iio
      · have h_zero : (fun w ↦ K (w, t)) = 0 := by
          ext w
          simp [K, S, ht]
        rw [h_zero]
        exact integrable_zero _ _ _
    · have h_norm_eq : (fun t ↦ ∫ w, ‖K (w, t)‖) =
          (Iic (0 : ℝ)).indicator (fun t ↦ |deriv f t| * gaussianPDFReal 0 1 t) := by
        ext t
        by_cases ht : t ≤ 0
        · have ht_mem : t ∈ Iic (0 : ℝ) := ht
          have h_slice : (fun w ↦ ‖K (w, t)‖) =
              (Iio t).indicator (fun w ↦ |deriv f t| * -(w * gaussianPDFReal 0 1 w)) := by
            ext w
            by_cases hwt : w < t
            · have hw0 : w ≤ 0 := le_of_lt (hwt.trans_le ht)
              have hφ0 : 0 ≤ gaussianPDFReal 0 1 w := gaussianPDFReal_nonneg 0 1 w
              simp [K, S, ht, hwt, abs_of_nonpos hw0, abs_of_nonneg hφ0]
            · simp [K, S, ht, hwt]
          rw [h_slice, integral_indicator measurableSet_Iio, integral_const_mul,
            integral_neg, steinLemma_integral_Iio_mul_pdf, neg_neg, indicator_of_mem ht_mem]
        · have ht_not : t ∉ Iic (0 : ℝ) := ht
          have h_zero : (fun w ↦ ‖K (w, t)‖) = 0 := by
            ext w
            simp [K, S, ht]
          rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem ht_not]
      rw [h_norm_eq]
      have h_abs : (fun t ↦ |deriv f t| * gaussianPDFReal 0 1 t) =
          fun t ↦ ‖deriv f t * gaussianPDFReal 0 1 t‖ := by
        ext t
        simp [abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
      rw [h_abs]
      exact hf'.norm.indicator measurableSet_Iic
  have h_left : (fun w ↦ ∫ t, K (w, t)) =
      (Iic (0 : ℝ)).indicator (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) := by
    ext w
    rcases lt_trichotomy w 0 with hw | rfl | hw
    · have h_slice : (fun t ↦ K (w, t)) =
          (Ioc w 0).indicator (fun t ↦ -deriv f t * (w * gaussianPDFReal 0 1 w)) := by
        ext t
        by_cases ht : w < t ∧ t ≤ 0 <;> simp [K, S, ht]
      have hw_mem : w ∈ Iic (0 : ℝ) := hw.le
      rw [h_slice, integral_indicator measurableSet_Ioc]
      simp_rw [neg_mul]
      rw [integral_neg, integral_mul_const, ← intervalIntegral.integral_of_le hw.le,
        (hf w 0).integral_deriv_eq_sub, indicator_of_mem hw_mem]
      ring
    · have h_zero : (fun t ↦ K (0, t)) = 0 := by
        ext t
        have hnot : ¬ (0 < t ∧ t ≤ 0) := fun h ↦ lt_irrefl 0 (h.1.trans_le h.2)
        simp [K, S, hnot]
      rw [h_zero, Pi.zero_def, integral_zero]
      simp
    · have h_zero : (fun t ↦ K (w, t)) = 0 := by
        ext t
        have hnot : ¬ (w < t ∧ t ≤ 0) := fun h ↦ lt_irrefl 0 ((hw.trans h.1).trans_le h.2)
        simp [K, S, hnot]
      have hw_not : w ∉ Iic (0 : ℝ) := not_le.mpr hw
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem hw_not]
  have h_right : (fun t ↦ ∫ w, K (w, t)) =
      (Iic (0 : ℝ)).indicator (fun t ↦ deriv f t * gaussianPDFReal 0 1 t) := by
    ext t
    by_cases ht : t ≤ 0
    · have h_slice : (fun w ↦ K (w, t)) =
          (Iio t).indicator (fun w ↦ -deriv f t * (w * gaussianPDFReal 0 1 w)) := by
        ext w
        by_cases hwt : w < t <;> simp [K, S, ht, hwt]
      have ht_mem : t ∈ Iic (0 : ℝ) := ht
      rw [h_slice, integral_indicator measurableSet_Iio, integral_const_mul,
        steinLemma_integral_Iio_mul_pdf, indicator_of_mem ht_mem]
      ring
    · have ht_not : t ∉ Iic (0 : ℝ) := ht
      have h_zero : (fun w ↦ K (w, t)) = 0 := by
        ext w
        simp [K, S, ht]
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem ht_not]
  have h_int_left :
      IntegrableOn (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) (Iic 0) volume :=
    (integrable_indicator_iff measurableSet_Iic).mp (h_left ▸ hK_int.integral_prod_left)
  refine ⟨h_int_left, ?_⟩
  have h_fub := (integral_prod K hK_int).symm.trans (integral_prod_symm K hK_int)
  rw [h_left, integral_indicator measurableSet_Iic, h_right,
    integral_indicator measurableSet_Iic] at h_fub
  exact h_fub

/-- **Fubini Integration-by-Parts Identity for $\mathcal{N}(0, 1)$**
(proof of Lemma 2.1(1) `\label{lem1}`, `SteinIntro.tex:628-636`):
if `f : ℝ → ℝ` is locally absolutely continuous (`∀ a b, AbsolutelyContinuousOnInterval f a b`)
and `deriv f` is integrable under `stdNormalLaw`, then `w ↦ w * f w` is integrable under
`stdNormalLaw` and `∫ w, w * f w ∂stdNormalLaw = ∫ t, deriv f t ∂stdNormalLaw`. -/
theorem integrable_mul_and_integral_eq_deriv_stdNormal {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (deriv f) stdNormalLaw) :
    Integrable (fun w ↦ w * f w) stdNormalLaw ∧
      ∫ w, w * f w ∂stdNormalLaw = ∫ t, deriv f t ∂stdNormalLaw := by
  have hf'_vol : Integrable (fun t ↦ deriv f t * gaussianPDFReal 0 1 t) volume :=
    steinLemma_integrable_stdNormal_iff.mp hf'
  obtain ⟨h_int_pos, h_eq_pos⟩ := steinLemma_integrableOn_and_integral_Ioi_pdf hf hf'_vol
  obtain ⟨h_int_neg, h_eq_neg⟩ := steinLemma_integrableOn_and_integral_Iic_pdf hf hf'_vol
  have h_int_sub : Integrable (fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w) volume := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact h_int_neg.union h_int_pos
  have h_eq_sub : ∫ w, w * (f w - f 0) * gaussianPDFReal 0 1 w =
      ∫ t, deriv f t * gaussianPDFReal 0 1 t := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi h_int_neg h_int_pos,
      h_eq_neg, h_eq_pos,
      ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hf'_vol.integrableOn hf'_vol.integrableOn,
      Iic_union_Ioi, setIntegral_univ]
  have h_decomp : (fun w ↦ w * f w * gaussianPDFReal 0 1 w) =
      fun w ↦ w * (f w - f 0) * gaussianPDFReal 0 1 w +
        f 0 * (w * gaussianPDFReal 0 1 w) := by
    ext w
    ring
  have h_int_const : Integrable (fun w ↦ f 0 * (w * gaussianPDFReal 0 1 w)) volume :=
    steinLemma_integrable_mul_pdf.const_mul (f 0)
  have h_int_full : Integrable (fun w ↦ w * f w * gaussianPDFReal 0 1 w) volume := by
    rw [h_decomp]
    exact h_int_sub.add h_int_const
  refine ⟨steinLemma_integrable_stdNormal_iff.mpr h_int_full, ?_⟩
  rw [steinLemma_integral_stdNormal_eq, steinLemma_integral_stdNormal_eq, h_decomp,
    integral_add h_int_sub h_int_const, h_eq_sub, integral_const_mul,
    steinLemma_integral_mul_pdf, mul_zero, add_zero]

end HalfLineFubini

/-- **Fubini Integrability Fact for $Z \sim \mathcal{N}(0, 1)$**
(proof of Lemma 2.1(1) `\label{lem1}`, `SteinIntro.tex:628-636`):
if `Z` is `P`-a.e. measurable with law `P.map Z = stdNormalLaw`, `f` is locally absolutely
continuous, and `ω ↦ deriv f (Z ω)` is `P`-integrable, then `ω ↦ Z ω * f (Z ω)` is
`P`-integrable. -/
theorem integrable_mul_of_integrable_deriv_stdNormal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : AEMeasurable Z P) (hZ_law : P.map Z = stdNormalLaw)
    {f : ℝ → ℝ} (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun ω ↦ deriv f (Z ω)) P) :
    Integrable (fun ω ↦ Z ω * f (Z ω)) P := by
  have hf'_map : Integrable (deriv f) (P.map Z) :=
    (integrable_map_measure (measurable_deriv f).aestronglyMeasurable hZ).mpr hf'
  have hf'_std : Integrable (deriv f) stdNormalLaw := by
    rwa [hZ_law] at hf'_map
  have h_wf_std : Integrable (fun w ↦ w * f w) stdNormalLaw :=
    (integrable_mul_and_integral_eq_deriv_stdNormal hf hf'_std).1
  have h_wf_map : Integrable (fun w ↦ w * f w) (P.map Z) := by
    rwa [hZ_law]
  exact h_wf_map.comp_aemeasurable hZ

/-- **Integrability of $\mathcal{A}f(Z)$ for $Z \sim \mathcal{N}(0, 1)$**
(Lemma 2.1(1) `\label{lem1}`, `SteinIntro.tex:562-569`, `628-636`):
under the hypotheses of Lemma 2.1(1), `ω ↦ normalSteinOp f (Z ω)` is `P`-integrable, ensuring
that `∫ ω, normalSteinOp f (Z ω) ∂P = 0` is a genuine Bochner expectation. -/
theorem integrable_normalSteinOp_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : AEMeasurable Z P) (hZ_law : P.map Z = stdNormalLaw)
    {f : ℝ → ℝ} (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun ω ↦ deriv f (Z ω)) P) :
    Integrable (fun ω ↦ normalSteinOp f (Z ω)) P := by
  change Integrable (fun ω ↦ deriv f (Z ω) - Z ω * f (Z ω)) P
  exact hf'.sub (integrable_mul_of_integrable_deriv_stdNormal P hZ hZ_law hf hf')

/-- **Lemma 2.1(1)** (`\label{lem1}` item 1, `SteinIntro.tex:562-569`, `628-636`):
if `Z` has standard normal law `P.map Z = stdNormalLaw`, `f : ℝ → ℝ` is locally absolutely
continuous, and `ω ↦ deriv f (Z ω)` is `P`-integrable, then
`∫ ω, normalSteinOp f (Z ω) ∂P = 0`. -/
theorem integral_normalSteinOp_eq_zero_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : AEMeasurable Z P) (hZ_law : P.map Z = stdNormalLaw)
    {f : ℝ → ℝ} (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun ω ↦ deriv f (Z ω)) P) :
    ∫ ω, normalSteinOp f (Z ω) ∂P = 0 := by
  have hf'_map : Integrable (deriv f) (P.map Z) :=
    (integrable_map_measure (measurable_deriv f).aestronglyMeasurable hZ).mpr hf'
  have hf'_std : Integrable (deriv f) stdNormalLaw := by
    rwa [hZ_law] at hf'_map
  obtain ⟨h_wf_std, h_eq_std⟩ := integrable_mul_and_integral_eq_deriv_stdNormal hf hf'_std
  have h_op_meas : Measurable (normalSteinOp f) := by
    change Measurable (fun w ↦ deriv f w - w * f w)
    exact (measurable_deriv f).sub
      (measurable_id.mul (steinLemma_continuous_of_ac hf).measurable)
  rw [← integral_map hZ h_op_meas.aestronglyMeasurable, hZ_law]
  change ∫ w, (deriv f w - w * f w) ∂stdNormalLaw = 0
  rw [integral_sub hf'_std h_wf_std, h_eq_std, sub_self]

section ConverseRamp

private def steinLemma_ramp (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (1 - ((n : ℝ) + 1) * (t - x)))

private lemma steinLemma_continuous_ramp (x : ℝ) (n : ℕ) : Continuous (steinLemma_ramp x n) := by
  unfold steinLemma_ramp
  fun_prop

private lemma steinLemma_ramp_nonneg (x : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ steinLemma_ramp x n t :=
  le_max_left 0 _

private lemma steinLemma_ramp_le_one (x : ℝ) (n : ℕ) (t : ℝ) : steinLemma_ramp x n t ≤ 1 :=
  max_le zero_le_one (min_le_left 1 _)

private lemma steinLemma_abs_ramp_le_one (x : ℝ) (n : ℕ) (t : ℝ) : |steinLemma_ramp x n t| ≤ 1 := by
  rw [abs_of_nonneg (steinLemma_ramp_nonneg x n t)]
  exact steinLemma_ramp_le_one x n t

private lemma steinLemma_tendsto_ramp (x t : ℝ) :
    Tendsto (fun n ↦ steinLemma_ramp x n t) atTop (𝓝 ((Iic x).indicator (1 : ℝ → ℝ) t)) := by
  by_cases htx : t ≤ x
  · have h_mem : t ∈ Iic x := htx
    rw [indicator_of_mem h_mem]
    have h_eq : ∀ n : ℕ, steinLemma_ramp x n t = 1 := by
      intro n
      have hsub : t - x ≤ 0 := sub_nonpos.mpr htx
      have hn : 0 ≤ (n : ℝ) + 1 := by positivity
      have hmul : ((n : ℝ) + 1) * (t - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn hsub
      have h1 : 1 ≤ 1 - ((n : ℝ) + 1) * (t - x) := by linarith
      simp [steinLemma_ramp, min_eq_left h1]
    simp_rw [h_eq]
    exact tendsto_const_nhds
  · have h_not : t ∉ Iic x := htx
    rw [indicator_of_notMem h_not]
    have hxt : 0 < t - x := sub_pos.mpr (lt_of_not_ge htx)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.Ici_mem_atTop ⌈(t - x)⁻¹⌉₊] with n hn
    have hceil : (t - x)⁻¹ ≤ (n : ℝ) :=
      (Nat.le_ceil (t - x)⁻¹).trans (Nat.cast_le.mpr hn)
    have hn1 : (t - x)⁻¹ ≤ (n : ℝ) + 1 := by linarith
    have hmul : 1 ≤ ((n : ℝ) + 1) * (t - x) := by
      have := mul_le_mul_of_nonneg_right hn1 hxt.le
      rwa [inv_mul_cancel₀ hxt.ne'] at this
    have hle0 : min 1 (1 - ((n : ℝ) + 1) * (t - x)) ≤ 0 :=
      (min_le_right 1 _).trans (by linarith)
    exact (max_eq_left hle0).symm

private lemma steinLemma_tendsto_integral_ramp (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    Tendsto (fun n ↦ ∫ t, steinLemma_ramp x n t ∂ν) atTop (𝓝 (cdf ν x)) := by
  have h_lim := tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ (1 : ℝ))
    (fun n ↦ (steinLemma_continuous_ramp x n).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n ↦ ae_of_all ν fun t ↦ by
      rw [Real.norm_eq_abs]
      exact steinLemma_abs_ramp_le_one x n t)
    (ae_of_all ν fun t ↦ steinLemma_tendsto_ramp x t)
  have h_ind : ∫ t, (Iic x).indicator (1 : ℝ → ℝ) t ∂ν = cdf ν x := by
    rw [integral_indicator measurableSet_Iic, Pi.one_def, setIntegral_const, smul_eq_mul,
      mul_one, ← cdf_eq_real]
  rwa [h_ind] at h_lim

/-- **Lemma 2.1(2)** (`\label{lem1}` item 2, `SteinIntro.tex:570-574`; ruling `D5` literal):
if `W` is `P`-a.e. measurable and `∫ ω, normalSteinOp f (W ω) ∂P = 0` holds for every locally
absolutely continuous `f : ℝ → ℝ` with `Integrable (deriv f) stdNormalLaw`, then
`P.map W = stdNormalLaw`. -/
theorem map_eq_stdNormalLaw_of_integral_normalSteinOp_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW : AEMeasurable W P)
    (hStein : ∀ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
      Integrable (deriv f) stdNormalLaw → ∫ ω, normalSteinOp f (W ω) ∂P = 0) :
    P.map W = stdNormalLaw := by
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  refine Measure.eq_of_cdf (P.map W) stdNormalLaw ?_
  ext x
  have h_eq_n : ∀ n : ℕ,
      ∫ t, steinLemma_ramp x n t ∂P.map W = ∫ z, steinLemma_ramp x n z ∂stdNormalLaw := by
    intro n
    obtain ⟨f, hf_ac, hf_int, hf_sol⟩ :=
      exists_ac_normalSteinSol_of_continuous_bounded
        (steinLemma_continuous_ramp x n) ⟨1, steinLemma_abs_ramp_le_one x n⟩
    have h0 : ∫ ω, normalSteinOp f (W ω) ∂P = 0 := hStein f hf_ac hf_int
    simp_rw [hf_sol] at h0
    have h_meas_W : AEStronglyMeasurable (fun ω ↦ steinLemma_ramp x n (W ω)) P :=
      ((steinLemma_continuous_ramp x n).measurable.comp_aemeasurable hW).aestronglyMeasurable
    have h_int_W : Integrable (fun ω ↦ steinLemma_ramp x n (W ω)) P :=
      (integrable_const (1 : ℝ)).mono' h_meas_W (ae_of_all P fun ω ↦ by
        rw [Real.norm_eq_abs]
        exact steinLemma_abs_ramp_le_one x n (W ω))
    have h_sub :
        ∫ ω, (steinLemma_ramp x n (W ω) - stdNormalExpect (steinLemma_ramp x n)) ∂P =
          (∫ ω, steinLemma_ramp x n (W ω) ∂P) - stdNormalExpect (steinLemma_ramp x n) := by
      rw [integral_sub h_int_W (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [h_sub, sub_eq_zero] at h0
    rw [integral_map hW (steinLemma_continuous_ramp x n).aestronglyMeasurable]
    exact h0
  have h_lim_W := steinLemma_tendsto_integral_ramp (P.map W) x
  have h_lim_Z := steinLemma_tendsto_integral_ramp stdNormalLaw x
  simp_rw [h_eq_n] at h_lim_W
  exact tendsto_nhds_unique h_lim_W h_lim_Z

end ConverseRamp

end SteinMethod
