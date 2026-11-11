/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.BerryEsseen.FejerKernel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lebesgue Integrability of `cdfDiff`, Fourier Identity, and Esseen–Fejér De-Smoothing
(`Formalization.BerryEsseen.FejerSmoothing`)

Proves Fubini integrability of $F_\mu(u) - \Phi(u)$ for any probability measure $\mu$ on
$\mathbb{R}$ with finite first moment, evaluates its Fourier transform
$\int_{\mathbb{R}} (F_\mu(u) - \Phi(u)) e^{i t u}\,du = \frac{e^{-t^2/2} - \varphi_\mu(t)}{i t}$
for $t \ne 0$, bounds the Fejér-smoothed CDF difference, and proves the refined Esseen de-smoothing
inequality with $2\alpha - 1$ denominator for **Theorem 1.1** (`\label{thm1}`,
`SteinIntro.tex:351-357`) in Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`).
-/

open Complex Filter Function MeasureTheory ProbabilityTheory Set
open scoped Real Topology

namespace SteinMethod.BerryEsseen

/-! ### Section 1: CDF Difference `cdfDiff`, Integrability on `ℝ`, and Fourier Transform -/

/-- Difference between the cumulative distribution function of `μ` and the standard normal CDF:
`cdfDiff μ u = μ.real (Iic u) - stdNormalCDF u`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
noncomputable def cdfDiff (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Iic u) - stdNormalCDF u

/-- Non-vacuity witness: `cdfDiff stdNormalLaw u = 0` for all `u : ℝ`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
@[simp]
theorem cdfDiff_stdNormalLaw (u : ℝ) : cdfDiff stdNormalLaw u = 0 := by
  simp [cdfDiff, stdNormalCDF, cdf_eq_real]

/-- Uniform bound `|cdfDiff μ u| ≤ 1` for any probability measure `μ` on `ℝ`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem abs_cdfDiff_le_one {μ : Measure ℝ} [IsProbabilityMeasure μ] (u : ℝ) :
    |cdfDiff μ u| ≤ 1 := by
  have h1 : 0 ≤ μ.real (Iic u) := measureReal_nonneg
  have h2 : μ.real (Iic u) ≤ 1 := by
    have := measureReal_mono (subset_univ (Iic u)) (μ := μ)
    rwa [probReal_univ] at this
  have h3 : 0 ≤ stdNormalCDF u := stdNormalCDF_nonneg u
  have h4 : stdNormalCDF u ≤ 1 := stdNormalCDF_le_one u
  rw [cdfDiff, abs_le]
  constructor <;> linarith

/-- Borel measurability of `cdfDiff μ` for any probability measure `μ` on `ℝ`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem measurable_cdfDiff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (cdfDiff μ) := by
  have heq : cdfDiff μ = fun u ↦ cdf μ u - stdNormalCDF u := by
    ext u; simp [cdfDiff, cdf_eq_real]
  rw [heq]
  exact (monotone_cdf μ).measurable.sub continuous_stdNormalCDF.measurable

private noncomputable def cdfDiffKernel (p : ℝ × ℝ) (u : ℝ) : ℝ :=
  (Iic u).indicator (1 : ℝ → ℝ) p.1 - (Iic u).indicator (1 : ℝ → ℝ) p.2

private theorem cdfDiffKernel_of_le {x z : ℝ} (hxz : x ≤ z) (u : ℝ) :
    cdfDiffKernel (x, z) u = (Ico x z).indicator (1 : ℝ → ℝ) u := by
  simp only [cdfDiffKernel, Set.indicator_apply, mem_Iic, mem_Ico, Pi.one_apply]
  by_cases hxu : x ≤ u
  · by_cases hzu : z ≤ u
    · simp [hxu, hzu]
    · have hmem : x ≤ u ∧ u < z := ⟨hxu, lt_of_not_ge hzu⟩
      simp [hxu, hzu, hmem]
  · have hzu : ¬ z ≤ u := fun h ↦ hxu (hxz.trans h)
    simp [hxu, hzu]

private theorem cdfDiffKernel_swap (p : ℝ × ℝ) (u : ℝ) :
    cdfDiffKernel (p.2, p.1) u = -cdfDiffKernel p u := by
  simp [cdfDiffKernel]

private theorem norm_cdfDiffKernel (p : ℝ × ℝ) (u : ℝ) :
    ‖cdfDiffKernel p u‖ = (Ico (min p.1 p.2) (max p.1 p.2)).indicator (1 : ℝ → ℝ) u := by
  have hind_nonneg : ∀ a b : ℝ, 0 ≤ (Ico a b).indicator (1 : ℝ → ℝ) u :=
    fun a b ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) u
  rcases le_total p.1 p.2 with hp | hp
  · rw [min_eq_left hp, max_eq_right hp, cdfDiffKernel_of_le hp, Real.norm_eq_abs,
      abs_of_nonneg (hind_nonneg p.1 p.2)]
  · have hswap : cdfDiffKernel p u = -cdfDiffKernel (p.2, p.1) u := by
      rw [cdfDiffKernel_swap, neg_neg]
    rw [min_eq_right hp, max_eq_left hp, hswap, cdfDiffKernel_of_le hp, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (hind_nonneg p.2 p.1)]

private theorem measurable_uncurry_cdfDiffKernel :
    Measurable (uncurry cdfDiffKernel) := by
  have heq : uncurry cdfDiffKernel =
      {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2}.indicator (1 : (ℝ × ℝ) × ℝ → ℝ) -
        {q : (ℝ × ℝ) × ℝ | q.1.2 ≤ q.2}.indicator (1 : (ℝ × ℝ) × ℝ → ℝ) := by
    ext ⟨⟨x, z⟩, u⟩
    simp [uncurry, cdfDiffKernel, Set.indicator_apply]
  rw [heq]
  have hs1 : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hs2 : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.2 ≤ q.2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  exact (measurable_const.indicator hs1).sub (measurable_const.indicator hs2)

private theorem integrable_uncurry_cdfDiffKernel
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h1 : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (uncurry cdfDiffKernel) ((μ.prod stdNormalLaw).prod volume) := by
  let ν : Measure (ℝ × ℝ) := μ.prod stdNormalLaw
  rw [integrable_prod_iff measurable_uncurry_cdfDiffKernel.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun p ↦ ?_, ?_⟩
  · have hIco : Integrable ((Ico (min p.1 p.2) (max p.1 p.2)).indicator (1 : ℝ → ℝ)) volume :=
      (integrable_indicator_iff measurableSet_Ico).mpr
        (IntegrableOn.of_bound measure_Ico_lt_top aestronglyMeasurable_const 1
          (Filter.Eventually.of_forall fun _ ↦ by simp))
    rcases le_total p.1 p.2 with hp | hp
    · simp_rw [uncurry, cdfDiffKernel_of_le hp]
      simpa [min_eq_left hp, max_eq_right hp] using hIco
    · have hswap : (fun u ↦ cdfDiffKernel p u) =
          fun u ↦ -(Ico p.2 p.1).indicator (1 : ℝ → ℝ) u := by
        ext u; rw [← cdfDiffKernel_of_le hp, cdfDiffKernel_swap, neg_neg]
      simp_rw [uncurry]; rw [hswap]
      simpa [min_eq_right hp, max_eq_left hp] using hIco.neg
  · have hnorm_int : (fun p : ℝ × ℝ ↦ ∫ u : ℝ, ‖uncurry cdfDiffKernel (p, u)‖) =
        fun p : ℝ × ℝ ↦ |p.1 - p.2| := by
      ext p
      simp_rw [uncurry, norm_cdfDiffKernel p]
      rw [integral_indicator_one measurableSet_Ico, measureReal_def, Real.volume_Ico,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max (a := p.1) (b := p.2))),
        max_sub_min_eq_abs, abs_sub_comm]
    rw [hnorm_int]
    have hp1 : Integrable (fun p : ℝ × ℝ ↦ p.1) ν := h1.comp_fst stdNormalLaw
    have hp2 : Integrable (fun p : ℝ × ℝ ↦ p.2) ν :=
      (memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := 1) 1)).comp_snd μ
    simpa [Real.norm_eq_abs] using (hp1.sub hp2).norm

private theorem integral_cdfDiffKernel_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] (u : ℝ) :
    ∫ p, cdfDiffKernel p u ∂(μ.prod stdNormalLaw) = cdfDiff μ u := by
  let f : ℝ → ℝ := (Iic u).indicator 1
  have hf_μ : Integrable f μ :=
    (integrable_indicator_iff measurableSet_Iic).mpr integrableOn_const
  have hf_φ : Integrable f stdNormalLaw :=
    (integrable_indicator_iff measurableSet_Iic).mpr integrableOn_const
  have hsub : ∫ p, cdfDiffKernel p u ∂(μ.prod stdNormalLaw) =
      (∫ p, f p.1 ∂(μ.prod stdNormalLaw)) - ∫ p, f p.2 ∂(μ.prod stdNormalLaw) :=
    integral_sub (hf_μ.comp_fst stdNormalLaw) (hf_φ.comp_snd μ)
  rw [hsub, integral_fun_fst f, integral_fun_snd f, probReal_univ, probReal_univ, one_smul,
    one_smul]
  have h1 : ∫ x, f x ∂μ = μ.real (Iic u) := integral_indicator_one measurableSet_Iic
  have h2 : ∫ z, f z ∂stdNormalLaw = stdNormalCDF u := stdNormalExpect_indicator_Iic u
  rw [h1, h2, cdfDiff]

/-- If `μ` is a probability measure on `ℝ` with finite first moment, then `cdfDiff μ` is
Lebesgue-integrable on `ℝ` (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integrable_cdfDiff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (cdfDiff μ) volume := by
  simpa [uncurry, integral_cdfDiffKernel_eq] using
    (integrable_uncurry_cdfDiffKernel h1).integral_prod_right

/-- Fourier transform of `cdfDiff μ` away from zero: for any probability measure `μ` on `ℝ` with
finite first moment and any `t ≠ 0`,
$\int_{\mathbb{R}} (F_\mu(u) - \Phi(u)) e^{i t u}\,du = \frac{e^{-t^2/2} - \varphi_\mu(t)}{i t}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_cdfDiff_mul_cexp {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ ↦ x) μ) {t : ℝ} (ht : t ≠ 0) :
    ∫ u : ℝ, (cdfDiff μ u : ℂ) * cexp ((t : ℂ) * (u : ℂ) * I) =
      (cexp (-(t : ℂ) ^ 2 / 2) - charFun μ t) / ((t : ℂ) * I) := by
  let ν : Measure (ℝ × ℝ) := μ.prod stdNormalLaw
  let G : (ℝ × ℝ) → ℝ → ℂ :=
    fun p u ↦ (cdfDiffKernel p u : ℂ) * cexp ((t : ℂ) * (u : ℂ) * I)
  have hG_int : Integrable (uncurry G) (ν.prod volume) := by
    refine (integrable_uncurry_cdfDiffKernel h1).norm.mono' ?_ ?_
    · have hm : Measurable (uncurry G) := by
        refine (ofRealCLM.measurable.comp measurable_uncurry_cdfDiffKernel).mul ?_
        have hc : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ cexp ((t : ℂ) * (q.2 : ℂ) * I)) := by
          fun_prop
        exact hc.measurable
      exact hm.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun q ↦ by
        simp only [uncurry, G, norm_mul, norm_real]
        rw [show (t : ℂ) * (q.2 : ℂ) * I = ((t * q.2 : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one]
  have hswap := integral_integral_swap hG_int
  have hrhs : (∫ u : ℝ, ∫ p, G p u ∂ν) =
      ∫ u : ℝ, (cdfDiff μ u : ℂ) * cexp ((t : ℂ) * (u : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [G, ν, integral_mul_const, integral_complex_ofReal, integral_cdfDiffKernel_eq]
  have htI : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
  have hin : ∀ p : ℝ × ℝ, (∫ u : ℝ, G p u) =
      (cexp ((t : ℂ) * (p.2 : ℂ) * I) - cexp ((t : ℂ) * (p.1 : ℂ) * I)) / ((t : ℂ) * I) := by
    intro ⟨x, z⟩
    have hint_ivl : (∫ u : ℝ, G (x, z) u) = ∫ u in x..z, cexp ((t : ℂ) * (u : ℂ) * I) := by
      rcases le_total x z with hxz | hzx
      · have heq : (fun u : ℝ ↦ G (x, z) u) =
            (Ico x z).indicator (fun u : ℝ ↦ cexp ((t : ℂ) * (u : ℂ) * I)) := by
          ext u
          simp only [G, cdfDiffKernel_of_le hxz]
          by_cases hu : u ∈ Ico x z <;> simp [hu]
        rw [heq, integral_indicator measurableSet_Ico,
          setIntegral_congr_set Ico_ae_eq_Ioc, intervalIntegral.integral_of_le hxz]
      · have heq : (fun u : ℝ ↦ G (x, z) u) =
            fun u ↦ -(Ico z x).indicator (fun u : ℝ ↦ cexp ((t : ℂ) * (u : ℂ) * I)) u := by
          ext u
          have hs : cdfDiffKernel (x, z) u = -cdfDiffKernel (z, x) u := by
            simp [cdfDiffKernel]
          simp only [G, hs, cdfDiffKernel_of_le hzx]
          by_cases hu : u ∈ Ico z x <;> simp [hu]
        rw [heq, integral_neg, integral_indicator measurableSet_Ico,
          setIntegral_congr_set Ico_ae_eq_Ioc, ← intervalIntegral.integral_of_le hzx,
          intervalIntegral.integral_symm, neg_neg]
    rw [hint_ivl]
    have hd : ∀ u : ℝ, HasDerivAt (fun s : ℝ ↦ cexp ((t : ℂ) * (s : ℂ) * I) / ((t : ℂ) * I))
        (cexp ((t : ℂ) * (u : ℂ) * I)) u := by
      intro u
      have hlin : HasDerivAt (fun s : ℝ ↦ (t : ℂ) * (s : ℂ) * I) ((t : ℂ) * I) u := by
        have h0 : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 u := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (1 : ℂ)
        convert (h0.const_mul (t : ℂ)).mul_const I using 1; ring
      convert hlin.cexp.div_const ((t : ℂ) * I) using 1
      exact (mul_div_cancel_right₀ _ htI).symm
    have hcont : Continuous (fun u : ℝ ↦ cexp ((t : ℂ) * (u : ℂ) * I)) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
      (hcont.intervalIntegrable x z), sub_div]
  have hlhs : (∫ p, (∫ u : ℝ, G p u) ∂ν) =
      (cexp (-(t : ℂ) ^ 2 / 2) - charFun μ t) / ((t : ℂ) * I) := by
    simp_rw [hin, integral_div]
    have he1 : Integrable (fun x : ℝ ↦ cexp ((t : ℂ) * (x : ℂ) * I)) μ :=
      Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x ↦ by
        rw [show (t : ℂ) * (x : ℂ) * I = ((t * x : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I])
    have he2 : Integrable (fun z : ℝ ↦ cexp ((t : ℂ) * (z : ℂ) * I)) stdNormalLaw :=
      Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun z ↦ by
        rw [show (t : ℂ) * (z : ℂ) * I = ((t * z : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I])
    rw [integral_sub (he2.comp_snd μ) (he1.comp_fst stdNormalLaw),
      integral_fun_snd (fun z : ℝ ↦ cexp ((t : ℂ) * (z : ℂ) * I)),
      integral_fun_fst (fun x : ℝ ↦ cexp ((t : ℂ) * (x : ℂ) * I)),
      probReal_univ, probReal_univ, one_smul, one_smul,
      ← charFun_apply_real, ← charFun_apply_real, stdNormalLaw,
      charFun_gaussianReal (μ := 0) (v := 1) t]
    simp [neg_div]
  rw [← hrhs, ← hswap, hlhs]

/-! ### Section 2: Fejér-Smoothed CDF Difference Bound -/

/-- Fejér-smoothed CDF difference bound: for any probability measure `μ` on `ℝ` with finite first
moment, `T > 0`, and `z : ℝ`,
$\left|\int_{\mathbb{R}} (F_\mu(z - y) - \Phi(z - y)) k_T(y)\,dy\right| \le
\frac{1}{\pi} \int_{(0, T]} \left(1 - \frac{t}{T}\right)
\frac{\|\varphi_\mu(t) - e^{-t^2/2}\|}{t}\,dt$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem abs_fejerSmooth_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ ↦ x) μ) {T : ℝ} (hT : 0 < T) (z : ℝ) :
    |∫ y : ℝ, cdfDiff μ (z - y) * fejerKernel T y| ≤
      1 / π * ∫ t in Ioc 0 T,
        (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) := by
  have hcdf_int : Integrable (cdfDiff μ) volume := integrable_cdfDiff h1
  let νT : Measure ℝ := volume.restrict (Icc (-T) T)
  have hνT_fin : IsFiniteMeasure νT := ⟨by simp [νT]⟩
  let H : ℝ → ℝ → ℂ := fun u t ↦
    (cdfDiff μ u : ℂ) * (1 / (2 * π) * (((1 - |t| / T : ℝ) : ℂ) *
      cexp (-(t : ℂ) * (z : ℂ) * I) * cexp ((t : ℂ) * (u : ℂ) * I)))
  have hH_int : Integrable (uncurry H) (volume.prod νT) := by
    refine (hcdf_int.norm.mul_prod (integrable_const (1 / (2 * π) : ℝ))).mono' ?_ ?_
    · have hm : Measurable (uncurry H) := by
        refine (ofRealCLM.measurable.comp
          ((measurable_cdfDiff μ).comp measurable_fst)).mul ?_
        have hc : Continuous (fun q : ℝ × ℝ ↦
            (1 / (2 * π) : ℂ) * (((1 - |q.2| / T : ℝ) : ℂ) *
              cexp (-(q.2 : ℂ) * (z : ℂ) * I) * cexp ((q.2 : ℂ) * (q.1 : ℂ) * I))) := by
          fun_prop
        exact hc.measurable
      exact hm.aestronglyMeasurable
    · have hae : ∀ᵐ q : ℝ × ℝ ∂(volume.prod νT), q.2 ∈ Icc (-T) T := by
        rw [ae_iff,
          show {q : ℝ × ℝ | q.2 ∉ Icc (-T) T} = univ ×ˢ (Icc (-T) T)ᶜ by ext q; simp,
          Measure.prod_prod, Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self,
          measure_empty, mul_zero]
      filter_upwards [hae] with q hq
      have habs_t : |q.2| ≤ T := abs_le.mpr hq
      have hw0 : 0 ≤ 1 - |q.2| / T := by
        have : |q.2| / T ≤ 1 := (div_le_one hT).mpr habs_t
        linarith
      have hw1 : 1 - |q.2| / T ≤ 1 := by
        have : 0 ≤ |q.2| / T := by positivity
        linarith
      simp only [uncurry, H, norm_mul, norm_real]
      have hc1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
        rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl,
          norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hc2 : ‖1 - |q.2| / T‖ = 1 - |q.2| / T := by
        rw [Real.norm_eq_abs, abs_of_nonneg hw0]
      have hc3 : ‖cexp (-(q.2 : ℂ) * (z : ℂ) * I)‖ = 1 := by
        rw [show -(q.2 : ℂ) * (z : ℂ) * I = ((-(q.2 * z) : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I]
      have hc4 : ‖cexp ((q.2 : ℂ) * (q.1 : ℂ) * I)‖ = 1 := by
        rw [show (q.2 : ℂ) * (q.1 : ℂ) * I = ((q.2 * q.1 : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I]
      rw [hc1, hc2, hc3, hc4, mul_one, mul_one]
      calc
        ‖cdfDiff μ q.1‖ * (1 / (2 * π) * (1 - |q.2| / T))
            ≤ ‖cdfDiff μ q.1‖ * (1 / (2 * π) * 1) := by gcongr
        _ = ‖cdfDiff μ q.1‖ * (1 / (2 * π)) := by ring
  have hconv_eq : ((∫ y : ℝ, cdfDiff μ (z - y) * fejerKernel T y : ℝ) : ℂ) =
      ∫ u : ℝ, ∫ t, H u t ∂νT := by
    have hsub := integral_sub_left_eq_self
      (fun u : ℝ ↦ cdfDiff μ u * fejerKernel T (z - u)) volume z
    simp only [sub_sub_cancel] at hsub
    rw [hsub, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    have heven : fejerKernel T (z - u) = fejerKernel T (u - z) := by
      rw [← fejerKernel_neg, neg_sub]
    dsimp only
    rw [ofReal_mul, heven, fejerKernel_eq_fourier hT (u - z)]
    change (cdfDiff μ u : ℂ) * (1 / (2 * π) * ∫ t,
        ((1 - |t| / T : ℝ) : ℂ) * cexp ((t : ℂ) * ((u - z : ℝ) : ℂ) * I) ∂νT) =
      ∫ t, H u t ∂νT
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    have hexp : cexp ((t : ℂ) * ((u - z : ℝ) : ℂ) * I) =
        cexp (-(t : ℂ) * (z : ℂ) * I) * cexp ((t : ℂ) * (u : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    simp only [H, hexp]; ring
  have hswap := integral_integral_swap hH_int
  let ψ : ℝ → ℝ := fun t ↦
    1 / (2 * π) * ((1 - |t| / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / |t|))
  have hae_ne : ∀ᵐ t : ℝ ∂νT, t ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  have hae_norm : ∀ᵐ t : ℝ ∂νT, ‖∫ u : ℝ, H u t‖ = ψ t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hae_ne] with t ht htnz
    have heq_u : (fun u : ℝ ↦ H u t) = fun u : ℝ ↦
        (1 / (2 * π) * (((1 - |t| / T : ℝ) : ℂ) * cexp (-(t : ℂ) * (z : ℂ) * I))) *
          ((cdfDiff μ u : ℂ) * cexp ((t : ℂ) * (u : ℂ) * I)) := by
      ext u; simp only [H]; ring
    rw [heq_u, integral_const_mul, integral_cdfDiff_mul_cexp h1 htnz]
    have habs_t : |t| ≤ T := abs_le.mpr ht
    have hw0 : 0 ≤ 1 - |t| / T := by
      have : |t| / T ≤ 1 := (div_le_one hT).mpr habs_t
      linarith
    have hc1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl,
        norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hc2 : ‖((1 - |t| / T : ℝ) : ℂ)‖ = 1 - |t| / T := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    have hc3 : ‖cexp (-(t : ℂ) * (z : ℂ) * I)‖ = 1 := by
      rw [show -(t : ℂ) * (z : ℂ) * I = ((-(t * z) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]
    have hc4 : ‖(cexp (-(t : ℂ) ^ 2 / 2) - charFun μ t) / ((t : ℂ) * I)‖ =
        ‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / |t| := by
      rw [norm_div, norm_sub_rev, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, hc1, hc2, hc3, hc4]
    simp only [ψ]; ring
  have hψ_int : IntegrableOn ψ (Icc (-T) T) :=
    (hH_int.swap.integral_prod_left.norm).congr hae_norm
  have hψ_even : ∀ t : ℝ, ψ (-t) = ψ t := by
    intro t
    have hcf : ‖charFun μ (-t) - cexp (-((-t : ℝ) : ℂ) ^ 2 / 2)‖ =
        ‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ := by
      have hcexp_conj : starRingEnd ℂ (cexp (-(t : ℂ) ^ 2 / 2)) =
          cexp (-((-t : ℝ) : ℂ) ^ 2 / 2) := by
        have hr : cexp (-(t : ℂ) ^ 2 / 2) = ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) := by
          rw [ofReal_exp]; congr 1; push_cast; ring
        have hr2 : cexp (-((-t : ℝ) : ℂ) ^ 2 / 2) = ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) := by
          rw [ofReal_exp]; congr 1; push_cast; ring
        rw [hr, hr2, Complex.conj_ofReal]
      rw [charFun_neg, ← hcexp_conj, ← map_sub, RCLike.norm_conj]
    simp only [ψ, abs_neg, hcf]
  have hfold : ∫ t in Icc (-T) T, ψ t =
      1 / π * ∫ t in Ioc 0 T,
        (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) := by
    have hivl_l : IntervalIntegrable ψ volume (-T) 0 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr
        (hψ_int.mono_set (Icc_subset_Icc_right hT.le))
    have hivl_r : IntervalIntegrable ψ volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr
        (hψ_int.mono_set (Icc_subset_Icc_left (by linarith)))
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals hivl_l hivl_r]
    have hneg : ∫ t in (-T)..(0 : ℝ), ψ t = ∫ t in (0 : ℝ)..T, ψ t := by
      have hc := intervalIntegral.integral_comp_neg ψ (a := -T) (b := 0)
      simp only [neg_zero, neg_neg, hψ_even] at hc
      exact hc
    rw [hneg, intervalIntegral.integral_of_le hT.le]
    have hpos_eq : ∫ t in Ioc 0 T, ψ t =
        1 / (2 * π) * ∫ t in Ioc 0 T,
          (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
      simp only [ψ, abs_of_pos ht.1]
    rw [hpos_eq]
    ring
  calc
    |∫ y : ℝ, cdfDiff μ (z - y) * fejerKernel T y|
        = ‖((∫ y : ℝ, cdfDiff μ (z - y) * fejerKernel T y : ℝ) : ℂ)‖ := by
          rw [norm_real, Real.norm_eq_abs]
    _ = ‖∫ t, (∫ u : ℝ, H u t) ∂νT‖ := by rw [hconv_eq, hswap]
    _ ≤ ∫ t, ‖∫ u : ℝ, H u t‖ ∂νT := norm_integral_le_integral_norm _
    _ = ∫ t in Icc (-T) T, ψ t := integral_congr_ae hae_norm
    _ = 1 / π * ∫ t in Ioc 0 T,
          (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) := hfold

/-! ### Section 3: Refined Esseen De-Smoothing Inequality with `2α - 1` Denominator -/

private theorem stdNormalCDF_sub_le {a b : ℝ} (hab : a ≤ b) :
    stdNormalCDF b - stdNormalCDF a ≤ (b - a) / √(2 * π) := by
  have hftc : ∫ s in a..b, stdNormalPDF s = stdNormalCDF b - stdNormalCDF a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hasDerivAt_stdNormalCDF s)
      (continuous_stdNormalPDF.intervalIntegrable a b)
  have hmono : ∫ s in a..b, stdNormalPDF s ≤ ∫ _ in a..b, (√(2 * π))⁻¹ :=
    intervalIntegral.integral_mono_on hab (continuous_stdNormalPDF.intervalIntegrable a b)
      intervalIntegrable_const (fun s _ ↦ by
        simpa [stdNormalPDF_zero] using stdNormalPDF_le_zero s)
  rw [hftc, intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at hmono
  exact hmono

/-- Refined Esseen–Fejér smoothing inequality at truncation radius $r = \frac{16}{5 T}$:
for any probability measure `μ` on `ℝ` with finite first moment, `T > 0`, and `x : ℝ`,
with $\alpha = \int_{(-r, r)} k_T(y)\,dy > 1 / 2$,
$|F_\mu(x) - \Phi(x)| \le \frac{1}{2\alpha - 1} \cdot \frac{1}{\pi} \int_{(0, T]}
(1 - t/T) \frac{\|\varphi_\mu(t) - e^{-t^2/2}\|}{t}\,dt +
\frac{\alpha}{2\alpha - 1} \cdot \frac{16 / (5 T)}{\sqrt{2\pi}}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem esseen_fejer_smoothing {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ ↦ x) μ) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    let r : ℝ := 16 / 5 / T
    let α : ℝ := ∫ y in Ioo (-r) r, fejerKernel T y
    |cdfDiff μ x| ≤
      1 / (2 * α - 1) * (1 / π * ∫ t in Ioc 0 T,
        (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)) +
      α / (2 * α - 1) * (r / √(2 * π)) := by
  intro r α
  have hr_pos : 0 < r := by positivity
  have hα_ge : (422368336 / 172265625 : ℝ) / π ≤ α := setIntegral_Ioo_fejerKernel_ge hT
  have hα_gt_half : 1 / 2 < α := by
    have hpi4 : π < 4 := Real.pi_lt_four
    have h1' : (422368336 / 172265625 : ℝ) / 4 < (422368336 / 172265625 : ℝ) / π :=
      div_lt_div_of_pos_left (by norm_num) Real.pi_pos hpi4
    linarith
  have hα_pos : 0 < α := by linarith
  have h2α_pos : 0 < 2 * α - 1 := by linarith
  let B : ℝ := 1 / π * ∫ t in Ioc 0 T,
    (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)
  let S : ℝ := sSup (range fun w : ℝ ↦ |cdfDiff μ w|)
  have hbdd : BddAbove (range fun w : ℝ ↦ |cdfDiff μ w|) :=
    ⟨1, by rintro _ ⟨w, rfl⟩; exact abs_cdfDiff_le_one w⟩
  have hle_S : ∀ w : ℝ, |cdfDiff μ w| ≤ S := fun w ↦ le_csSup hbdd ⟨w, rfl⟩
  have hS_nonneg : 0 ≤ S := (abs_nonneg (cdfDiff μ 0)).trans (hle_S 0)
  have hk_int : Integrable (fejerKernel T) volume := integrable_fejerKernel hT
  have hk_compl : ∫ y in (Ioo (-r) r)ᶜ, fejerKernel T y = 1 - α := by
    have hsum := integral_add_compl (s := Ioo (-r) r) measurableSet_Ioo hk_int
    rw [integral_fejerKernel hT] at hsum
    dsimp only [α]; linarith
  have htail_bound : ∀ z : ℝ,
      |∫ y in (Ioo (-r) r)ᶜ, cdfDiff μ (z - y) * fejerKernel T y| ≤ (1 - α) * S := by
    intro z
    have hgz_int : Integrable (fun y : ℝ ↦ cdfDiff μ (z - y) * fejerKernel T y) volume := by
      refine hk_int.mono' ?_ ?_
      · exact (((measurable_cdfDiff μ).comp (measurable_const.sub measurable_id)).mul
          (continuous_fejerKernel T).measurable).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerKernel_nonneg hT.le y)]
          exact mul_le_of_le_one_left (fejerKernel_nonneg hT.le y) (abs_cdfDiff_le_one _)
    calc
      |∫ y in (Ioo (-r) r)ᶜ, cdfDiff μ (z - y) * fejerKernel T y|
          ≤ ∫ y in (Ioo (-r) r)ᶜ, ‖cdfDiff μ (z - y) * fejerKernel T y‖ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := fun y ↦ cdfDiff μ (z - y) * fejerKernel T y)
      _ ≤ ∫ y in (Ioo (-r) r)ᶜ, S * fejerKernel T y := by
        refine setIntegral_mono_on hgz_int.norm.integrableOn (hk_int.const_mul S).integrableOn
          measurableSet_Ioo.compl fun y _ ↦ ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerKernel_nonneg hT.le y)]
        exact mul_le_mul_of_nonneg_right (hle_S (z - y)) (fejerKernel_nonneg hT.le y)
      _ = S * ∫ y in (Ioo (-r) r)ᶜ, fejerKernel T y := integral_const_mul _ _
      _ = (1 - α) * S := by rw [hk_compl]; ring
  have hlocal_bound : ∀ z : ℝ,
      |∫ y in Ioo (-r) r, cdfDiff μ (z - y) * fejerKernel T y| ≤ B + (1 - α) * S := by
    intro z
    have hgz_int : Integrable (fun y : ℝ ↦ cdfDiff μ (z - y) * fejerKernel T y) volume := by
      refine hk_int.mono' ?_ ?_
      · exact (((measurable_cdfDiff μ).comp (measurable_const.sub measurable_id)).mul
          (continuous_fejerKernel T).measurable).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerKernel_nonneg hT.le y)]
          exact mul_le_of_le_one_left (fejerKernel_nonneg hT.le y) (abs_cdfDiff_le_one _)
    have hsplit := integral_add_compl (s := Ioo (-r) r) measurableSet_Ioo hgz_int
    have hsm : |∫ y : ℝ, cdfDiff μ (z - y) * fejerKernel T y| ≤ B := abs_fejerSmooth_le h1 hT z
    have htl := htail_bound z
    rw [abs_le] at hsm htl ⊢
    constructor <;> linarith
  have hy_int : IntegrableOn (fun y : ℝ ↦ y * fejerKernel T y) (Ioo (-r) r) := by
    have hc : Continuous (fun y : ℝ ↦ y * fejerKernel T y) := by fun_prop
    exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hpt_all : ∀ w : ℝ, |cdfDiff μ w| ≤ (B + α * (r / √(2 * π)) + (1 - α) * S) / α := by
    intro w
    rw [le_div_iff₀ hα_pos]
    rcases le_or_gt 0 (cdfDiff μ w) with hw | hw
    · let z : ℝ := w + r
      have hmono : ∫ y in Ioo (-r) r, (cdfDiff μ w - (r - y) / √(2 * π)) * fejerKernel T y ≤
          ∫ y in Ioo (-r) r, cdfDiff μ (z - y) * fejerKernel T y := by
        have hl_int : IntegrableOn
            (fun y : ℝ ↦ (cdfDiff μ w - (r - y) / √(2 * π)) * fejerKernel T y) (Ioo (-r) r) := by
          have heq : (fun y : ℝ ↦ (cdfDiff μ w - (r - y) / √(2 * π)) * fejerKernel T y) =
              fun y ↦ (cdfDiff μ w - r / √(2 * π)) * fejerKernel T y +
                (1 / √(2 * π)) * (y * fejerKernel T y) := by ext y; ring
          rw [heq]
          exact (hk_int.integrableOn.const_mul _).add (hy_int.const_mul _)
        have hr_int : IntegrableOn (fun y : ℝ ↦ cdfDiff μ (z - y) * fejerKernel T y)
            (Ioo (-r) r) := by
          refine hk_int.integrableOn.mono' ?_ ?_
          · exact (((measurable_cdfDiff μ).comp (measurable_const.sub measurable_id)).mul
              (continuous_fejerKernel T).measurable).aestronglyMeasurable
          · exact Filter.Eventually.of_forall fun y ↦ by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerKernel_nonneg hT.le y)]
              exact mul_le_of_le_one_left (fejerKernel_nonneg hT.le y) (abs_cdfDiff_le_one _)
        refine setIntegral_mono_on hl_int hr_int measurableSet_Ioo fun y hy ↦ ?_
        have hwz : w ≤ z - y := by simp only [z]; linarith [hy.2]
        have hμ_le : μ.real (Iic w) ≤ μ.real (Iic (z - y)) :=
          measureReal_mono (Iic_subset_Iic.mpr hwz)
        have hΦ_le : stdNormalCDF (z - y) - stdNormalCDF w ≤ (r - y) / √(2 * π) := by
          simpa [z, add_sub_assoc, add_sub_cancel_left] using stdNormalCDF_sub_le hwz
        have hdiff : cdfDiff μ w - (r - y) / √(2 * π) ≤ cdfDiff μ (z - y) := by
          simp only [cdfDiff]; linarith
        exact mul_le_mul_of_nonneg_right hdiff (fejerKernel_nonneg hT.le y)
      have hlhs_eval : ∫ y in Ioo (-r) r, (cdfDiff μ w - (r - y) / √(2 * π)) * fejerKernel T y =
          (cdfDiff μ w - r / √(2 * π)) * α := by
        have heq : (fun y : ℝ ↦ (cdfDiff μ w - (r - y) / √(2 * π)) * fejerKernel T y) =
            fun y ↦ (cdfDiff μ w - r / √(2 * π)) * fejerKernel T y +
              (1 / √(2 * π)) * (y * fejerKernel T y) := by ext y; ring
        rw [heq, integral_add (hk_int.integrableOn.const_mul _) (hy_int.const_mul _),
          integral_const_mul, integral_const_mul, setIntegral_Ioo_mul_fejerKernel_eq_zero T r,
          mul_zero, add_zero]
      have hub : ∫ y in Ioo (-r) r, cdfDiff μ (z - y) * fejerKernel T y ≤ B + (1 - α) * S :=
        (le_abs_self _).trans (hlocal_bound z)
      rw [abs_of_nonneg hw]
      linarith
    · let z : ℝ := w - r
      have hmono : ∫ y in Ioo (-r) r, (-cdfDiff μ w - (r + y) / √(2 * π)) * fejerKernel T y ≤
          ∫ y in Ioo (-r) r, (-cdfDiff μ (z - y)) * fejerKernel T y := by
        have hl_int : IntegrableOn
            (fun y : ℝ ↦ (-cdfDiff μ w - (r + y) / √(2 * π)) * fejerKernel T y) (Ioo (-r) r) := by
          have heq : (fun y : ℝ ↦ (-cdfDiff μ w - (r + y) / √(2 * π)) * fejerKernel T y) =
              fun y ↦ (-cdfDiff μ w - r / √(2 * π)) * fejerKernel T y -
                (1 / √(2 * π)) * (y * fejerKernel T y) := by ext y; ring
          rw [heq]
          exact (hk_int.integrableOn.const_mul _).sub (hy_int.const_mul _)
        have hr_int : IntegrableOn (fun y : ℝ ↦ (-cdfDiff μ (z - y)) * fejerKernel T y)
            (Ioo (-r) r) := by
          refine hk_int.integrableOn.mono' ?_ ?_
          · exact (((measurable_cdfDiff μ).comp (measurable_const.sub measurable_id)).neg.mul
              (continuous_fejerKernel T).measurable).aestronglyMeasurable
          · exact Filter.Eventually.of_forall fun y ↦ by
              rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (fejerKernel_nonneg hT.le y)]
              exact mul_le_of_le_one_left (fejerKernel_nonneg hT.le y) (abs_cdfDiff_le_one _)
        refine setIntegral_mono_on hl_int hr_int measurableSet_Ioo fun y hy ↦ ?_
        have hzw : z - y ≤ w := by simp only [z]; linarith [hy.1]
        have hμ_le : μ.real (Iic (z - y)) ≤ μ.real (Iic w) :=
          measureReal_mono (Iic_subset_Iic.mpr hzw)
        have hΦ_le : stdNormalCDF w - stdNormalCDF (z - y) ≤ (r + y) / √(2 * π) := by
          have hlen : w - (z - y) = r + y := by simp only [z]; ring
          simpa [hlen] using stdNormalCDF_sub_le hzw
        have hdiff : -cdfDiff μ w - (r + y) / √(2 * π) ≤ -cdfDiff μ (z - y) := by
          simp only [cdfDiff]; linarith
        exact mul_le_mul_of_nonneg_right hdiff (fejerKernel_nonneg hT.le y)
      have hlhs_eval : ∫ y in Ioo (-r) r, (-cdfDiff μ w - (r + y) / √(2 * π)) * fejerKernel T y =
          (-cdfDiff μ w - r / √(2 * π)) * α := by
        have heq : (fun y : ℝ ↦ (-cdfDiff μ w - (r + y) / √(2 * π)) * fejerKernel T y) =
            fun y ↦ (-cdfDiff μ w - r / √(2 * π)) * fejerKernel T y -
              (1 / √(2 * π)) * (y * fejerKernel T y) := by ext y; ring
        rw [heq, integral_sub (hk_int.integrableOn.const_mul _) (hy_int.const_mul _),
          integral_const_mul, integral_const_mul, setIntegral_Ioo_mul_fejerKernel_eq_zero T r,
          mul_zero, sub_zero]
      have hub : ∫ y in Ioo (-r) r, (-cdfDiff μ (z - y)) * fejerKernel T y ≤ B + (1 - α) * S := by
        have hneg_eq : (∫ y in Ioo (-r) r, (-cdfDiff μ (z - y)) * fejerKernel T y) =
            -∫ y in Ioo (-r) r, cdfDiff μ (z - y) * fejerKernel T y := by
          simp_rw [neg_mul, integral_neg]
        rw [hneg_eq]
        exact (neg_le_abs _).trans (hlocal_bound z)
      rw [abs_of_neg hw]
      linarith
  have hS_le : S ≤ (B + α * (r / √(2 * π)) + (1 - α) * S) / α :=
    csSup_le (range_nonempty _) (by rintro _ ⟨w, rfl⟩; exact hpt_all w)
  have hS_mul : α * S ≤ B + α * (r / √(2 * π)) + (1 - α) * S := by
    have := (le_div_iff₀ hα_pos).mp hS_le
    linarith
  have hS_final : S ≤ 1 / (2 * α - 1) * B + α / (2 * α - 1) * (r / √(2 * π)) := by
    have h2 : S * (2 * α - 1) ≤ B + α * (r / √(2 * π)) := by linarith
    rw [← le_div_iff₀ h2α_pos] at h2
    refine h2.trans_eq ?_
    ring
  exact (hle_S x).trans hS_final

end SteinMethod.BerryEsseen
