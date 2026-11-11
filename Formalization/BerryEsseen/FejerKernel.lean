/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.MillRatio
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-!
# Fejér Kernel Calculus, Normalization, and Mass Concentration
(`Formalization.BerryEsseen.FejerKernel`)

Defines the unit and $T$-scaled Fejér probability densities on $\mathbb{R}$ and proves their
continuity, integrability, Fourier representation, unit total mass $\int_{\mathbb{R}} k_T = 1$,
oddness cancellation $\int_{-r}^r y k_T(y)\,dy = 0$, and degree-8 cosine lower bound at
$R = 16 / 5$ for **Theorem 1.1** (`\label{thm1}`, `SteinIntro.tex:351-357`) in Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`).
-/

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Real Topology

namespace SteinMethod.BerryEsseen

/-! ### Section 1: Definition, Continuity, Formula Away from Zero, and Integrability -/

/-- Unit Fejér density $k_1(u) = \frac{1}{2\pi} \operatorname{sinc}(u / 2)^2$, coinciding with
$\frac{1 - \cos u}{\pi u^2}$ for $u \ne 0$ and $\frac{1}{2\pi}$ at $u = 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
noncomputable def fejerKernelOne (u : ℝ) : ℝ :=
  1 / (2 * π) * (Real.sinc (u / 2)) ^ 2

/-- Scaled Fejér density $k_T(y) = T k_1(T y)$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
noncomputable def fejerKernel (T y : ℝ) : ℝ :=
  T * fejerKernelOne (T * y)

/-- Value $k_1(0) = \frac{1}{2\pi}$ (non-vacuity witness; Theorem 1.1 `\label{thm1}`,
`SteinIntro.tex:351-357`). -/
@[simp]
theorem fejerKernelOne_zero : fejerKernelOne 0 = 1 / (2 * π) := by
  simp [fejerKernelOne]

/-- Continuity of `fejerKernelOne` (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
@[fun_prop]
theorem continuous_fejerKernelOne : Continuous fejerKernelOne := by
  unfold fejerKernelOne; fun_prop

/-- Continuity of `fejerKernel T` (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
@[fun_prop]
theorem continuous_fejerKernel (T : ℝ) : Continuous (fejerKernel T) := by
  unfold fejerKernel; fun_prop

/-- Nonnegativity $0 \le k_1(u)$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem fejerKernelOne_nonneg (u : ℝ) : 0 ≤ fejerKernelOne u := by
  unfold fejerKernelOne; positivity

/-- Nonnegativity $0 \le k_T(y)$ for $T \ge 0$ (Theorem 1.1 `\label{thm1}`,
`SteinIntro.tex:351-357`). -/
theorem fejerKernel_nonneg {T : ℝ} (hT : 0 ≤ T) (y : ℝ) : 0 ≤ fejerKernel T y :=
  mul_nonneg hT (fejerKernelOne_nonneg _)

/-- Evenness $k_1(-u) = k_1(u)$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
@[simp]
theorem fejerKernelOne_neg (u : ℝ) : fejerKernelOne (-u) = fejerKernelOne u := by
  simp [fejerKernelOne, neg_div]

/-- Evenness $k_T(-y) = k_T(y)$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
@[simp]
theorem fejerKernel_neg (T y : ℝ) : fejerKernel T (-y) = fejerKernel T y := by
  simp [fejerKernel]

/-- Uniform bound $k_1(u) \le \frac{1}{2\pi}$ (Theorem 1.1 `\label{thm1}`,
`SteinIntro.tex:351-357`). -/
theorem fejerKernelOne_le (u : ℝ) : fejerKernelOne u ≤ 1 / (2 * π) := by
  unfold fejerKernelOne
  have hs : (Real.sinc (u / 2)) ^ 2 ≤ 1 := by
    have h1 := Real.abs_sinc_le_one (u / 2)
    nlinarith [abs_le.mp h1]
  exact mul_le_of_le_one_right (by positivity) hs

/-- Explicit formula $k_1(u) = \frac{1 - \cos u}{\pi u^2}$ for $u \ne 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem fejerKernelOne_eq_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    fejerKernelOne u = (1 - Real.cos u) / (π * u ^ 2) := by
  have hu2 : u / 2 ≠ 0 := by positivity
  rw [fejerKernelOne, Real.sinc_of_ne_zero hu2]
  have hcos : 1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
    have h1 : Real.cos u = Real.cos (2 * (u / 2)) := by ring_nf
    rw [h1, Real.cos_two_mul]
    have h2 := Real.sin_sq_add_cos_sq (u / 2)
    linarith
  rw [hcos]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Pointwise Cauchy domination $k_1(u) \le \frac{4}{\pi} (1 + u^2)^{-1}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem fejerKernelOne_le_cauchy (u : ℝ) :
    fejerKernelOne u ≤ 4 / π * (1 + u ^ 2)⁻¹ := by
  have hpi : 0 < π := Real.pi_pos
  have h1u : 0 < 1 + u ^ 2 := by positivity
  rcases le_or_gt (u ^ 2) 1 with hu | hu
  · have h1 : fejerKernelOne u ≤ 1 / (2 * π) := fejerKernelOne_le u
    have h2 : (1 / 2 : ℝ) ≤ (1 + u ^ 2)⁻¹ := by
      rw [one_div, inv_le_inv₀ (by norm_num) h1u]
      linarith
    have h3 : 1 / (2 * π) ≤ 4 / π * (1 / 2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    exact h1.trans (h3.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
  · have hunz : u ≠ 0 := by
      intro h; subst h; norm_num at hu
    rw [fejerKernelOne_eq_of_ne_zero hunz]
    have hcos : 1 - Real.cos u ≤ 2 := by linarith [Real.neg_one_le_cos u]
    have h1 : (1 - Real.cos u) / (π * u ^ 2) ≤ 2 / (π * u ^ 2) :=
      div_le_div_of_nonneg_right hcos (by positivity)
    have h2 : 2 / (π * u ^ 2) ≤ 4 / π * (1 + u ^ 2)⁻¹ := by
      rw [show 4 / π * (1 + u ^ 2)⁻¹ = 4 / (π * (1 + u ^ 2)) by field_simp,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact h1.trans h2

/-- Integrability of `fejerKernelOne` on $\mathbb{R}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integrable_fejerKernelOne : Integrable fejerKernelOne := by
  refine (integrable_inv_one_add_sq.const_mul (4 / π)).mono'
    continuous_fejerKernelOne.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u ↦ by
    rw [Real.norm_of_nonneg (fejerKernelOne_nonneg u)]
    exact fejerKernelOne_le_cauchy u

/-- Integrability of `fejerKernel T` for $T > 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integrable_fejerKernel {T : ℝ} (hT : 0 < T) : Integrable (fejerKernel T) :=
  (integrable_fejerKernelOne.comp_mul_left' hT.ne').const_mul T

/-! ### Section 2: Cosine and Complex Exponential Fourier Representations -/

/-- Cosine integral representation $k_1(u) = \frac{1}{\pi} \int_0^1 (1 - t) \cos(t u)\,dt$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem fejerKernelOne_eq_integral_cos (u : ℝ) :
    fejerKernelOne u = 1 / π * ∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (t * u) := by
  by_cases hu : u = 0
  · subst hu
    have hint : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
      have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ s - s ^ 2 / 2) (1 - t) t := fun t ↦ by
        convert (hasDerivAt_id' t).fun_sub ((hasDerivAt_pow 2 t).div_const 2) using 1
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
        ((continuous_const.sub continuous_id').intervalIntegrable 0 1)]
      norm_num
    simp [fejerKernelOne, hint]
  · rw [fejerKernelOne_eq_of_ne_zero hu]
    have hd : ∀ t : ℝ,
        HasDerivAt (fun s : ℝ ↦ (1 - s) * Real.sin (s * u) / u - Real.cos (s * u) / u ^ 2)
          ((1 - t) * Real.cos (t * u)) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
      have h2 : HasDerivAt (fun s : ℝ ↦ Real.sin (s * u)) (Real.cos (t * u) * u) t := by
        have hp : HasDerivAt (fun s : ℝ ↦ s * u) u t := by
          simpa using (hasDerivAt_id' t).mul_const u
        exact hp.sin
      have h3 : HasDerivAt (fun s : ℝ ↦ Real.cos (s * u)) (-Real.sin (t * u) * u) t := by
        have hp : HasDerivAt (fun s : ℝ ↦ s * u) u t := by
          simpa using (hasDerivAt_id' t).mul_const u
        exact hp.cos
      convert ((h1.fun_mul h2).div_const u).fun_sub (h3.div_const (u ^ 2)) using 1
      field_simp; ring
    have hcont : Continuous (fun t : ℝ ↦ (1 - t) * Real.cos (t * u)) := by fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      (hcont.intervalIntegrable 0 1)
    rw [hftc]
    simp only [sub_self, zero_mul, zero_div, one_mul, zero_sub, Real.cos_zero, Real.sin_zero]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp; ring

/-- Complex Fourier representation
$(k_T(y) : \mathbb{C}) = \frac{1}{2\pi} \int_{[-T, T]} (1 - |t|/T) e^{i t y}\,dt$ for $T > 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem fejerKernel_eq_fourier {T : ℝ} (hT : 0 < T) (y : ℝ) :
    (fejerKernel T y : ℂ) =
      1 / (2 * π) * ∫ t in Icc (-T) T, ((1 - |t| / T : ℝ) : ℂ) * cexp ((t : ℂ) * (y : ℂ) * I) := by
  let g : ℝ → ℂ := fun t ↦ ((1 - |t| / T : ℝ) : ℂ) * cexp ((t : ℂ) * (y : ℂ) * I)
  have hg_cont : Continuous g := by unfold g; fun_prop
  have hIcc : ∫ t in Icc (-T) T, g t = ∫ t in (-T)..T, g t := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  have hadj : ∫ t in (-T)..T, g t = (∫ t in (-T)..(0 : ℝ), g t) + ∫ t in (0 : ℝ)..T, g t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (-T) 0) (hg_cont.intervalIntegrable 0 T)).symm
  have hneg : ∫ t in (-T)..(0 : ℝ), g t = ∫ t in (0 : ℝ)..T, g (-t) := by
    simp [intervalIntegral.integral_comp_neg]
  have hsum : (∫ t in (0 : ℝ)..T, g (-t)) + (∫ t in (0 : ℝ)..T, g t) =
      ∫ t in (0 : ℝ)..T, (g (-t) + g t) :=
    (intervalIntegral.integral_add ((hg_cont.comp continuous_neg).intervalIntegrable 0 T)
      (hg_cont.intervalIntegrable 0 T)).symm
  have hpair : ∀ t ∈ uIcc 0 T,
      g (-t) + g t = (2 : ℂ) * (((1 - t / T) * Real.cos (t * y) : ℝ) : ℂ) := by
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    have habs : |t| = t := abs_of_nonneg ht.1
    have hcos : cexp (((-(t * y) : ℝ) : ℂ) * I) + cexp (((t * y : ℝ) : ℂ) * I) =
        2 * (Real.cos (t * y) : ℂ) := by
      rw [Complex.exp_mul_I, Complex.exp_mul_I]
      push_cast; simp; ring
    have he1 : ((-t : ℝ) : ℂ) * (y : ℂ) * I = ((-(t * y) : ℝ) : ℂ) * I := by push_cast; ring
    have he2 : (t : ℂ) * (y : ℂ) * I = ((t * y : ℝ) : ℂ) * I := by push_cast; ring
    calc
      g (-t) + g t = ((1 - t / T : ℝ) : ℂ) *
          (cexp (((-(t * y) : ℝ) : ℂ) * I) + cexp (((t * y : ℝ) : ℂ) * I)) := by
        simp only [g, abs_neg, habs, he1, he2]; ring
      _ = ((1 - t / T : ℝ) : ℂ) * (2 * (Real.cos (t * y) : ℂ)) := by rw [hcos]
      _ = (2 : ℂ) * (((1 - t / T) * Real.cos (t * y) : ℝ) : ℂ) := by push_cast; ring
  have hint_pair : ∫ t in (0 : ℝ)..T, (g (-t) + g t) =
      (2 : ℂ) * ((∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * y) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr hpair, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal]
  have hscale : ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * y) =
      T * ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * (T * y)) := by
    have h2 := intervalIntegral.integral_comp_mul_left
      (fun t ↦ (1 - t / T) * Real.cos (t * y)) (a := 0) (b := 1) hT.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at h2
    have hcongr : ∫ s in (0 : ℝ)..1, (1 - T * s / T) * Real.cos (T * s * y) =
        ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * (T * y)) := by
      refine intervalIntegral.integral_congr fun s _ ↦ ?_
      have hd : T * s / T = s := mul_div_cancel_left₀ s hT.ne'
      rw [hd, show T * s * y = s * (T * y) by ring]
    calc
      ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * y)
          = T * (T⁻¹ * ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * y)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
      _ = T * ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * (T * y)) := by
            rw [← h2, hcongr]
  change (fejerKernel T y : ℂ) = 1 / (2 * π) * ∫ t in Icc (-T) T, g t
  rw [hIcc, hadj, hneg, hsum, hint_pair, hscale, fejerKernel,
    fejerKernelOne_eq_integral_cos (T * y)]
  push_cast
  ring

/-! ### Section 3: Normalization $\int_{\mathbb{R}} k_1(u)\,du = 1$ via Gaussian Fubini + DCT -/

private theorem integral_exp_mul_cos_gaussian {M : ℝ} (hM : 0 < M) (t : ℝ) :
    ∫ u : ℝ, Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u) =
      √(2 * π) * M * Real.exp (-M ^ 2 * t ^ 2 / 2) := by
  let v : NNReal := ⟨M ^ 2, sq_nonneg M⟩
  have hv : v ≠ 0 := by
    intro h
    have : (v : ℝ) = 0 := congr_arg NNReal.toReal h
    have hM2 : M ^ 2 = 0 := this
    nlinarith
  have hcf := charFun_gaussianReal (μ := 0) (v := v) t
  rw [charFun_apply_real, integral_gaussianReal_eq_integral_smul hv] at hcf
  have hint : Integrable (fun x : ℝ ↦ gaussianPDFReal 0 v x • cexp ((t : ℂ) * (x : ℂ) * I)) := by
    refine (integrable_gaussianPDFReal 0 v).mono' ?_ ?_
    · exact (continuous_ofReal.comp (by fun_prop) |>.smul (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x ↦ by
        rw [norm_smul, Real.norm_of_nonneg (gaussianPDFReal_nonneg 0 v x),
          show (t : ℂ) * (x : ℂ) * I = ((t * x : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one]
  have hv_coe : (v : ℝ) = M ^ 2 := rfl
  have hre := congr_arg Complex.reCLM hcf
  rw [← Complex.reCLM.integral_comp_comm hint] at hre
  have hrhs_re : Complex.reCLM (cexp ((t : ℂ) * (0 : ℝ) * I - (v : ℂ) * (t : ℂ) ^ 2 / 2)) =
      Real.exp (-M ^ 2 * t ^ 2 / 2) := by
    have harg : (t : ℂ) * (0 : ℝ) * I - (v : ℂ) * (t : ℂ) ^ 2 / 2 =
        ((-M ^ 2 * t ^ 2 / 2 : ℝ) : ℂ) := by
      rw [hv_coe]; push_cast; ring
    rw [Complex.reCLM_apply, harg, ← ofReal_exp, ofReal_re]
  rw [hrhs_re] at hre
  have hlhs_re : (∫ x : ℝ, Complex.reCLM (gaussianPDFReal 0 v x • cexp ((t : ℂ) * (x : ℂ) * I))) =
      (√(2 * π) * M)⁻¹ * ∫ u : ℝ, Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u) := by
    have hpt : (fun x : ℝ ↦ Complex.reCLM
          (gaussianPDFReal 0 v x • cexp ((t : ℂ) * (x : ℂ) * I))) =
        fun u : ℝ ↦ (√(2 * π) * M)⁻¹ *
          (Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u)) := by
      ext u
      have hsq : √(2 * π * M ^ 2) = √(2 * π) * M := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le]
      have hexp_re : (cexp ((t : ℂ) * (u : ℂ) * I)).re = Real.cos (t * u) := by
        rw [Complex.exp_mul_I]
        simp [← ofReal_mul, ← ofReal_cos, ← ofReal_sin]
      simp only [Complex.reCLM_apply, Complex.real_smul, mul_re, ofReal_re, ofReal_im, zero_mul,
        sub_zero, hexp_re, gaussianPDFReal, hv_coe]
      rw [hsq]
      ring
    rw [hpt, integral_const_mul]
  rw [hlhs_re] at hre
  have hpos : (√(2 * π) * M) ≠ 0 := by positivity
  calc
    ∫ u : ℝ, Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u)
        = (√(2 * π) * M) * ((√(2 * π) * M)⁻¹ *
            ∫ u : ℝ, Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos, one_mul]
    _ = √(2 * π) * M * Real.exp (-M ^ 2 * t ^ 2 / 2) := by rw [hre]

private theorem integral_fejerKernelOne_mul_gaussian {M : ℝ} (hM : 0 < M) :
    ∫ u : ℝ, fejerKernelOne u * Real.exp (-u ^ 2 / (2 * M ^ 2)) =
      2 * stdNormalCDF M - 1 + 2 / M * (stdNormalPDF M - stdNormalPDF 0) := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hν_fin : IsFiniteMeasure ν := ⟨by simp [ν]⟩
  let F : ℝ → ℝ → ℝ := fun u t ↦
    1 / π * (1 - t) * Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u)
  have hF_int : Integrable (Function.uncurry F) (volume.prod ν) := by
    have hb_u : Integrable (fun u : ℝ ↦ Real.exp (-(1 / (2 * M ^ 2)) * u ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by positivity)
    have hb_t : Integrable (fun _ : ℝ ↦ (1 / π : ℝ)) ν := integrable_const _
    refine (hb_u.mul_prod hb_t).mono' ?_ ?_
    · have hcont : Continuous (Function.uncurry F) := by
        unfold Function.uncurry F; fun_prop
      exact hcont.aestronglyMeasurable
    · have hae : ∀ᵐ p : ℝ × ℝ ∂(volume.prod ν), p.2 ∈ Icc (0 : ℝ) 1 := by
        rw [ae_iff,
          show {p : ℝ × ℝ | p.2 ∉ Icc (0 : ℝ) 1} = univ ×ˢ (Icc (0 : ℝ) 1)ᶜ by ext p; simp,
          Measure.prod_prod, Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self,
          measure_empty, mul_zero]
      filter_upwards [hae] with p hp
      have ht1 : |1 - p.2| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
      have hcos : |Real.cos (p.2 * p.1)| ≤ 1 := Real.abs_cos_le_one _
      simp only [Function.uncurry, F, Real.norm_eq_abs, abs_mul,
        abs_of_pos (div_pos one_pos Real.pi_pos), abs_of_pos (Real.exp_pos _)]
      have hexp_eq : Real.exp (-p.1 ^ 2 / (2 * M ^ 2)) =
          Real.exp (-(1 / (2 * M ^ 2)) * p.1 ^ 2) := by ring_nf
      rw [hexp_eq]
      calc
        1 / π * |1 - p.2| * Real.exp (-(1 / (2 * M ^ 2)) * p.1 ^ 2) * |Real.cos (p.2 * p.1)|
            ≤ 1 / π * 1 * Real.exp (-(1 / (2 * M ^ 2)) * p.1 ^ 2) * 1 := by
          gcongr
        _ = Real.exp (-(1 / (2 * M ^ 2)) * p.1 ^ 2) * (1 / π) := by ring
  have hswap := integral_integral_swap hF_int
  have hlhs : (∫ u : ℝ, ∫ t, F u t ∂ν) =
      ∫ u : ℝ, fejerKernelOne u * Real.exp (-u ^ 2 / (2 * M ^ 2)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    have heq : (fun t : ℝ ↦ F u t) =
        fun t ↦ Real.exp (-u ^ 2 / (2 * M ^ 2)) * (1 / π * ((1 - t) * Real.cos (t * u))) := by
      ext t; simp only [F]; ring
    change (∫ t in Icc (0 : ℝ) 1, F u t) = _
    rw [heq, integral_const_mul, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, ← fejerKernelOne_eq_integral_cos u]
    ring
  have hrhs : (∫ t, ∫ u : ℝ, F u t ∂volume ∂ν) =
      2 * stdNormalCDF M - 1 + 2 / M * (stdNormalPDF M - stdNormalPDF 0) := by
    have hin : ∀ t : ℝ, (∫ u : ℝ, F u t) = 2 * ((1 - t) * M * stdNormalPDF (M * t)) := by
      intro t
      have heq : (fun u : ℝ ↦ F u t) =
          fun u ↦ (1 / π * (1 - t)) * (Real.exp (-u ^ 2 / (2 * M ^ 2)) * Real.cos (t * u)) := by
        ext u; simp only [F]; ring
      rw [heq, integral_const_mul, integral_exp_mul_cos_gaussian hM t, stdNormalPDF_eq]
      have hexp_eq : -(M * t) ^ 2 / 2 = -M ^ 2 * t ^ 2 / 2 := by ring
      rw [hexp_eq]
      calc
        1 / π * (1 - t) * (√(2 * π) * M * Real.exp (-M ^ 2 * t ^ 2 / 2))
            = (√(2 * π) * √(2 * π)) * ((2 * π)⁻¹ *
                (2 * ((1 - t) * M * Real.exp (-M ^ 2 * t ^ 2 / 2)))) * (√(2 * π))⁻¹ := by
              have hpi : π ≠ 0 := Real.pi_ne_zero
              have hsq0 : √(2 * π) ≠ 0 := by positivity
              field_simp
        _ = 2 * ((1 - t) * M * ((√(2 * π))⁻¹ * Real.exp (-M ^ 2 * t ^ 2 / 2))) := by
              rw [Real.mul_self_sqrt (by positivity)]
              have hpi : π ≠ 0 := Real.pi_ne_zero
              field_simp
    change (∫ t in Icc (0 : ℝ) 1, ∫ u : ℝ, F u t) = _
    simp_rw [hin]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul]
    have hd : ∀ t : ℝ,
        HasDerivAt (fun s : ℝ ↦ stdNormalCDF (M * s) + 1 / M * stdNormalPDF (M * s))
          ((1 - t) * M * stdNormalPDF (M * t)) t := by
      intro t
      have hlin : HasDerivAt (fun s : ℝ ↦ M * s) M t := by
        simpa using (hasDerivAt_id' t).const_mul M
      have h1 : HasDerivAt (fun s : ℝ ↦ stdNormalCDF (M * s)) (stdNormalPDF (M * t) * M) t :=
        (hasDerivAt_stdNormalCDF (M * t)).comp t hlin
      have h2 : HasDerivAt (fun s : ℝ ↦ stdNormalPDF (M * s))
          ((-(M * t) * stdNormalPDF (M * t)) * M) t :=
        (hasDerivAt_stdNormalPDF (M * t)).comp t hlin
      convert h1.fun_add (h2.const_mul (1 / M)) using 1
      field_simp; ring
    have hcont : Continuous (fun t : ℝ ↦ (1 - t) * M * stdNormalPDF (M * t)) := by fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      (hcont.intervalIntegrable 0 1)
    rw [hftc, mul_one, mul_zero, stdNormalCDF_zero]
    ring
  linarith [hswap, hlhs, hrhs]

/-- Unit total mass $\int_{\mathbb{R}} k_1(u)\,du = 1$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_fejerKernelOne : ∫ u : ℝ, fejerKernelOne u = 1 := by
  let f : ℕ → ℝ → ℝ := fun m u ↦
    fejerKernelOne u * Real.exp (-u ^ 2 / (2 * ((m : ℝ) + 1) ^ 2))
  have hlhs : Tendsto (fun m : ℕ ↦ ∫ u : ℝ, f m u) atTop (𝓝 (∫ u : ℝ, fejerKernelOne u)) := by
    refine tendsto_integral_of_dominated_convergence fejerKernelOne
      (fun m ↦ ?_) integrable_fejerKernelOne (fun m ↦ ?_) ?_
    · have hc : Continuous (f m) := by unfold f; fun_prop
      exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u ↦ by
        simp only [f, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (fejerKernelOne_nonneg u), abs_of_pos (Real.exp_pos _)]
        have hexp : Real.exp (-u ^ 2 / (2 * ((m : ℝ) + 1) ^ 2)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg u)) (by positivity))
        exact mul_le_of_le_one_right (fejerKernelOne_nonneg u) hexp
    · exact Filter.Eventually.of_forall fun u ↦ by
        have harg : Tendsto (fun m : ℕ ↦ -u ^ 2 / (2 * ((m : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
          have hden : Tendsto (fun m : ℕ ↦ 2 * ((m : ℝ) + 1) ^ 2) atTop atTop :=
            Tendsto.const_mul_atTop (by norm_num)
              ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
                (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
          exact tendsto_const_nhds.div_atTop hden
        simpa [f] using ((Real.continuous_exp.tendsto 0).comp harg).const_mul (fejerKernelOne u)
  have hrhs : Tendsto (fun m : ℕ ↦ ∫ u : ℝ, f m u) atTop (𝓝 1) := by
    have heq : (fun m : ℕ ↦ ∫ u : ℝ, f m u) = fun m : ℕ ↦
        2 * stdNormalCDF ((m : ℝ) + 1) - 1 +
          2 / ((m : ℝ) + 1) * (stdNormalPDF ((m : ℝ) + 1) - stdNormalPDF 0) := by
      ext m
      exact integral_fejerKernelOne_mul_gaussian (by positivity)
    rw [heq]
    have hM_top : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hcdf : Tendsto (fun m : ℕ ↦ 2 * stdNormalCDF ((m : ℝ) + 1) - 1) atTop (𝓝 1) := by
      have h0 := ((tendsto_stdNormalCDF_atTop.comp hM_top).const_mul 2).sub_const 1
      norm_num at h0
      exact h0
    have hpdf : Tendsto (fun m : ℕ ↦
        2 / ((m : ℝ) + 1) * (stdNormalPDF ((m : ℝ) + 1) - stdNormalPDF 0)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ ↦ 2 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hM_top
      have h2 : Tendsto (fun m : ℕ ↦ stdNormalPDF ((m : ℝ) + 1) - stdNormalPDF 0)
          atTop (𝓝 (0 - stdNormalPDF 0)) := by
        have hp0 : Tendsto stdNormalPDF atTop (𝓝 0) := by
          simpa using tendsto_pow_mul_stdNormalPDF_atTop 0
        exact (hp0.comp hM_top).sub_const _
      simpa using h1.mul h2
    simpa using hcdf.add hpdf
  exact tendsto_nhds_unique hlhs hrhs

/-- Unit total mass $\int_{\mathbb{R}} k_T(y)\,dy = 1$ for $T > 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ y : ℝ, fejerKernel T y = 1 := by
  unfold fejerKernel
  rw [integral_const_mul, Measure.integral_comp_mul_left fejerKernelOne T,
    abs_of_pos (inv_pos.mpr hT), smul_eq_mul, integral_fejerKernelOne, mul_one,
    mul_inv_cancel₀ hT.ne']

/-! ### Section 4: Oddness Cancellation and Degree-8 Cosine Mass Bound at $R = 16 / 5$ -/

/-- Oddness cancellation $\int_{(-r, r)} y k_T(y)\,dy = 0$ for all $T, r \in \mathbb{R}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem setIntegral_Ioo_mul_fejerKernel_eq_zero (T r : ℝ) :
    ∫ y in Ioo (-r) r, y * fejerKernel T y = 0 := by
  rcases le_or_gt r 0 with hr | hr
  · have hemp : Ioo (-r) r = ∅ := Ioo_eq_empty (by linarith)
    simp [hemp]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    let h : ℝ → ℝ := fun y ↦ y * fejerKernel T y
    have hh_cont : Continuous h := by unfold h; fun_prop
    have hadj : ∫ y in (-r)..r, h y = (∫ y in (-r)..(0 : ℝ), h y) + ∫ y in (0 : ℝ)..r, h y :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hh_cont.intervalIntegrable (-r) 0) (hh_cont.intervalIntegrable 0 r)).symm
    have hneg : ∫ y in (-r)..(0 : ℝ), h y = ∫ y in (0 : ℝ)..r, h (-y) := by
      simp [intervalIntegral.integral_comp_neg]
    have hodd : ∀ y : ℝ, h (-y) = -h y := fun y ↦ by simp [h]
    change ∫ y in (-r)..r, h y = 0
    rw [hadj, hneg]
    simp_rw [hodd, intervalIntegral.integral_neg]
    linarith

private theorem nonneg_of_deriv_nonneg (f f' : ℝ → ℝ) (hf0 : f 0 = 0)
    (hd : ∀ s : ℝ, HasDerivAt f (f' s) s) (hcont : Continuous f')
    (hpos : ∀ s : ℝ, 0 ≤ s → 0 ≤ f' s) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ f u := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    (hcont.intervalIntegrable 0 u)
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..u, f' s :=
    intervalIntegral.integral_nonneg hu fun s hs ↦ hpos s hs.1
  rw [hftc, hf0, sub_zero] at h0
  exact h0

/-- Alternating degree-8 Taylor lower bound
$1 - \cos u \ge \frac{u^2}{2} - \frac{u^4}{24} + \frac{u^6}{720} - \frac{u^8}{40320}$
for all $u \in \mathbb{R}$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem one_sub_cos_ge_deg8 (u : ℝ) :
    u ^ 2 / 2 - u ^ 4 / 24 + u ^ 6 / 720 - u ^ 8 / 40320 ≤ 1 - Real.cos u := by
  suffices h : ∀ x : ℝ, 0 ≤ x →
      x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 - x ^ 8 / 40320 ≤ 1 - Real.cos x by
    rcases le_or_gt 0 u with hu | hu
    · exact h u hu
    · have hnu := h (-u) (by linarith)
      rw [Real.cos_neg] at hnu
      have h2 : (-u) ^ 2 = u ^ 2 := by ring
      have h4 : (-u) ^ 4 = u ^ 4 := by ring
      have h6 : (-u) ^ 6 = u ^ 6 := by ring
      have h8 : (-u) ^ 8 = u ^ 8 := by ring
      linarith
  intro x hx
  have c1 : ∀ s : ℝ, 0 ≤ s → 0 ≤ s - Real.sin s := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ t - Real.sin t) (fun t ↦ 1 - Real.cos t)
      (by simp)
      (fun t ↦ by
        convert (hasDerivAt_id' t).fun_sub (hasDerivAt_id' t).sin using 1; ring)
      (by fun_prop) (fun t _ ↦ by linarith [Real.cos_le_one t]) hs
  have c2 : ∀ s : ℝ, 0 ≤ s → 0 ≤ Real.cos s - (1 - s ^ 2 / 2) := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ Real.cos t - (1 - t ^ 2 / 2)) (fun t ↦ t - Real.sin t)
      (by simp)
      (fun t ↦ by
        convert (hasDerivAt_id' t).cos.fun_sub
          ((hasDerivAt_const t (1 : ℝ)).fun_sub ((hasDerivAt_pow 2 t).div_const 2)) using 1
        ring)
      (by fun_prop) (fun t ht ↦ c1 t ht) hs
  have c3 : ∀ s : ℝ, 0 ≤ s → 0 ≤ Real.sin s - (s - s ^ 3 / 6) := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ Real.sin t - (t - t ^ 3 / 6))
      (fun t ↦ Real.cos t - (1 - t ^ 2 / 2))
      (by simp)
      (fun t ↦ by
        convert (hasDerivAt_id' t).sin.fun_sub
          ((hasDerivAt_id' t).fun_sub ((hasDerivAt_pow 3 t).div_const 6)) using 1
        norm_num; ring)
      (by fun_prop) (fun t ht ↦ c2 t ht) hs
  have c4 : ∀ s : ℝ, 0 ≤ s → 0 ≤ (1 - s ^ 2 / 2 + s ^ 4 / 24) - Real.cos s := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
      (fun t ↦ Real.sin t - (t - t ^ 3 / 6))
      (by simp)
      (fun t ↦ by
        convert (((hasDerivAt_const t (1 : ℝ)).fun_sub
          ((hasDerivAt_pow 2 t).div_const 2)).fun_add
          ((hasDerivAt_pow 4 t).div_const 24)).fun_sub (hasDerivAt_id' t).cos using 1
        norm_num; ring)
      (by fun_prop) (fun t ht ↦ c3 t ht) hs
  have c5 : ∀ s : ℝ, 0 ≤ s → 0 ≤ (s - s ^ 3 / 6 + s ^ 5 / 120) - Real.sin s := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
      (fun t ↦ (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
      (by simp)
      (fun t ↦ by
        convert (((hasDerivAt_id' t).fun_sub
          ((hasDerivAt_pow 3 t).div_const 6)).fun_add
          ((hasDerivAt_pow 5 t).div_const 120)).fun_sub (hasDerivAt_id' t).sin using 1
        norm_num; ring)
      (by fun_prop) (fun t ht ↦ c4 t ht) hs
  have c6 : ∀ s : ℝ, 0 ≤ s →
      0 ≤ Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720) := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (fun t ↦ (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
      (by simp)
      (fun t ↦ by
        convert (hasDerivAt_id' t).cos.fun_sub
          ((((hasDerivAt_const t (1 : ℝ)).fun_sub ((hasDerivAt_pow 2 t).div_const 2)).fun_add
            ((hasDerivAt_pow 4 t).div_const 24)).fun_sub
            ((hasDerivAt_pow 6 t).div_const 720)) using 1
        norm_num; ring)
      (by fun_prop) (fun t ht ↦ c5 t ht) hs
  have c7 : ∀ s : ℝ, 0 ≤ s →
      0 ≤ Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040) := fun s hs ↦
    nonneg_of_deriv_nonneg (fun t ↦ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
      (fun t ↦ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (by simp)
      (fun t ↦ by
        convert (hasDerivAt_id' t).sin.fun_sub
          ((((hasDerivAt_id' t).fun_sub ((hasDerivAt_pow 3 t).div_const 6)).fun_add
            ((hasDerivAt_pow 5 t).div_const 120)).fun_sub
            ((hasDerivAt_pow 7 t).div_const 5040)) using 1
        norm_num; ring)
      (by fun_prop) (fun t ht ↦ c6 t ht) hs
  have c8 := nonneg_of_deriv_nonneg
    (fun t ↦ (1 - Real.cos t) - (t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 - t ^ 8 / 40320))
    (fun t ↦ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
    (by norm_num)
    (fun t ↦ by
      convert ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t).cos).fun_sub
        ((((hasDerivAt_pow 2 t).div_const 2).fun_sub
          ((hasDerivAt_pow 4 t).div_const 24)).fun_add
          ((hasDerivAt_pow 6 t).div_const 720) |>.fun_sub
            ((hasDerivAt_pow 8 t).div_const 40320)) using 1
      norm_num; ring)
    (by fun_prop) (fun t ht ↦ c7 t ht) hx
  linarith

/-- Lower bound on the central Fejér mass at $R = 16 / 5$:
$\int_{(-16/(5T), 16/(5T))} k_T(y)\,dy \ge \frac{422368336}{172265625 \, \pi}$ for $T > 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem setIntegral_Ioo_fejerKernel_ge {T : ℝ} (hT : 0 < T) :
    (422368336 / 172265625 : ℝ) / π ≤
      ∫ y in Ioo (-(16 / 5 / T)) (16 / 5 / T), fejerKernel T y := by
  have hr_pos : 0 < 16 / 5 / T := by positivity
  have hscale : ∫ y in Ioo (-(16 / 5 / T)) (16 / 5 / T), fejerKernel T y =
      ∫ u in (-(16 / 5 : ℝ))..(16 / 5 : ℝ), fejerKernelOne u := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : -(16 / 5 / T) ≤ 16 / 5 / T)]
    unfold fejerKernel
    rw [intervalIntegral.integral_const_mul]
    have hcomp := intervalIntegral.integral_comp_mul_left fejerKernelOne
      (a := -(16 / 5 / T)) (b := 16 / 5 / T) hT.ne'
    simp only [smul_eq_mul, mul_neg, mul_div_cancel₀ _ hT.ne'] at hcomp
    rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  rw [hscale]
  let p : ℝ → ℝ := fun u ↦ (1 / 2 - u ^ 2 / 24 + u ^ 4 / 720 - u ^ 6 / 40320) / π
  have hp_le : ∀ u : ℝ, p u ≤ fejerKernelOne u := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [p, fejerKernelOne]; ring_nf; rfl
    · rw [fejerKernelOne_eq_of_ne_zero hu]
      have hdeg8 := one_sub_cos_ge_deg8 u
      have hp_eq : p u = (u ^ 2 / 2 - u ^ 4 / 24 + u ^ 6 / 720 - u ^ 8 / 40320) / (π * u ^ 2) := by
        simp only [p]; field_simp
      rw [hp_eq]
      exact div_le_div_of_nonneg_right hdeg8 (by positivity)
  have hp_cont : Continuous p := by unfold p; fun_prop
  have hmono : ∫ u in (-(16 / 5 : ℝ))..(16 / 5 : ℝ), p u ≤
      ∫ u in (-(16 / 5 : ℝ))..(16 / 5 : ℝ), fejerKernelOne u :=
    intervalIntegral.integral_mono_on (by norm_num)
      (hp_cont.intervalIntegrable _ _)
      (continuous_fejerKernelOne.intervalIntegrable _ _)
      (fun u _ ↦ hp_le u)
  have hp_int : ∫ u in (-(16 / 5 : ℝ))..(16 / 5 : ℝ), p u = (422368336 / 172265625 : ℝ) / π := by
    have hd : ∀ u : ℝ,
        HasDerivAt (fun s : ℝ ↦ (s / 2 - s ^ 3 / 72 + s ^ 5 / 3600 - s ^ 7 / 282240) / π)
          (p u) u := by
      intro u
      convert (((((hasDerivAt_id' u).div_const 2).fun_sub
        ((hasDerivAt_pow 3 u).div_const 72)).fun_add
        ((hasDerivAt_pow 5 u).div_const 3600)).fun_sub
        ((hasDerivAt_pow 7 u).div_const 282240)).div_const π using 1
      simp only [p]; norm_num; ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
      (hp_cont.intervalIntegrable (-(16 / 5)) (16 / 5))
    rw [hftc]
    ring
  rwa [hp_int] at hmono

end SteinMethod.BerryEsseen
