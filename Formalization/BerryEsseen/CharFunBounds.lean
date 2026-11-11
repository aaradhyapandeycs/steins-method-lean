/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.BerryEsseen.Cantelli
import Mathlib.Probability.CentralLimitTheorem

/-!
# Characteristic Function Taylor and Gaussian Integral Bounds
(`Formalization.BerryEsseen.CharFunBounds`)

Proves quantitative third-moment characteristic function estimates and half-line Gaussian moment
formulas for the small-$\beta$ ($\beta = \rho / \sqrt{n} < 3 / 10$, $n \ge 12$) regime of
**Theorem 1.1** (`\label{thm1}`, `SteinIntro.tex:351-357`) in Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`).
-/

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Real Topology

namespace SteinMethod.BerryEsseen

/-! ### Section 1: Elementary Complex Exponential and Real Gaussian Taylor Bounds -/

private theorem norm_cexp_mul_I_sub_quad_le_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    ‖cexp ((y : ℂ) * I) - (1 + (y : ℂ) * I - (y : ℂ) ^ 2 / 2)‖ ≤ y ^ 3 / 6 := by
  have hd0 : ∀ s : ℝ, HasDerivAt (fun t : ℝ ↦ cexp ((t : ℂ) * I) - 1)
      (I * cexp ((s : ℂ) * I)) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * I) I s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const I
    simpa [mul_comm I] using h1.cexp.sub_const (1 : ℂ)
  have hb0 : ∀ t : ℝ, 0 ≤ t → ‖cexp ((t : ℂ) * I) - 1‖ ≤ t := by
    intro t ht
    have hcont0 : Continuous (fun s : ℝ ↦ I * cexp ((s : ℂ) * I)) := by fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd0 s)
      (hcont0.intervalIntegrable 0 t)
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at hftc
    rw [← hftc]
    calc
      ‖∫ s in (0 : ℝ)..t, I * cexp ((s : ℂ) * I)‖
          ≤ ∫ s in (0 : ℝ)..t, ‖I * cexp ((s : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) :=
        intervalIntegral.integral_mono_on ht (hcont0.norm.intervalIntegrable 0 t)
          intervalIntegrable_const (fun s _ ↦ by
            rw [norm_mul, norm_I, one_mul, norm_exp_ofReal_mul_I])
      _ = t := by simp
  have hd1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ ↦ cexp ((t : ℂ) * I) - (1 + (t : ℂ) * I))
      (I * (cexp ((s : ℂ) * I) - 1)) s := by
    intro s
    have hlin : HasDerivAt (fun t : ℝ ↦ (1 : ℂ) + (t : ℂ) * I) I s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const I).const_add (1 : ℂ)
    have hexp : HasDerivAt (fun t : ℝ ↦ cexp ((t : ℂ) * I)) (I * cexp ((s : ℂ) * I)) s := by
      have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * I) I s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const I
      simpa [mul_comm I] using h1.cexp
    convert hexp.fun_sub hlin using 1; ring
  have hb1 : ∀ t : ℝ, 0 ≤ t → ‖cexp ((t : ℂ) * I) - (1 + (t : ℂ) * I)‖ ≤ t ^ 2 / 2 := by
    intro t ht
    have hcont1 : Continuous (fun s : ℝ ↦ I * (cexp ((s : ℂ) * I) - 1)) := by fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd1 s)
      (hcont1.intervalIntegrable 0 t)
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, add_zero, sub_self, sub_zero] at hftc
    rw [← hftc]
    calc
      ‖∫ s in (0 : ℝ)..t, I * (cexp ((s : ℂ) * I) - 1)‖
          ≤ ∫ s in (0 : ℝ)..t, ‖I * (cexp ((s : ℂ) * I) - 1)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, s :=
        intervalIntegral.integral_mono_on ht (hcont1.norm.intervalIntegrable 0 t)
          (continuous_id.intervalIntegrable 0 t) (fun s hs ↦ by
            rw [norm_mul, norm_I, one_mul]
            exact hb0 s hs.1)
      _ = t ^ 2 / 2 := by simp
  have hd2 : ∀ s : ℝ,
      HasDerivAt (fun t : ℝ ↦ cexp ((t : ℂ) * I) - (1 + (t : ℂ) * I - (t : ℂ) ^ 2 / 2))
        (I * (cexp ((s : ℂ) * I) - (1 + (s : ℂ) * I))) s := by
    intro s
    have hlin0 : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (1 : ℂ)
    have hq : HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ 2 / 2) (s : ℂ) s := by
      have hsq : HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ 2) ((s : ℂ) + (s : ℂ)) s := by
        simpa [sq] using hlin0.fun_mul hlin0
      convert hsq.div_const (2 : ℂ) using 1; ring
    have hprev := (hd1 s).fun_add hq
    have hfn : (fun t : ℝ ↦ cexp ((t : ℂ) * I) - (1 + (t : ℂ) * I) + (t : ℂ) ^ 2 / 2) =
        fun t : ℝ ↦ cexp ((t : ℂ) * I) - (1 + (t : ℂ) * I - (t : ℂ) ^ 2 / 2) := by
      ext t; ring
    rw [hfn] at hprev
    convert hprev using 1
    calc
      I * (cexp ((s : ℂ) * I) - (1 + (s : ℂ) * I))
          = I * (cexp ((s : ℂ) * I) - 1) - (s : ℂ) * I ^ 2 := by ring
      _ = I * (cexp ((s : ℂ) * I) - 1) + (s : ℂ) := by rw [I_sq]; ring
  have hcont2 : Continuous (fun s : ℝ ↦ I * (cexp ((s : ℂ) * I) - (1 + (s : ℂ) * I))) := by
    fun_prop
  have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd2 s)
    (hcont2.intervalIntegrable 0 y)
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, sub_zero, sub_self] at hftc2
  rw [← hftc2]
  calc
    ‖∫ s in (0 : ℝ)..y, I * (cexp ((s : ℂ) * I) - (1 + (s : ℂ) * I))‖
        ≤ ∫ s in (0 : ℝ)..y, ‖I * (cexp ((s : ℂ) * I) - (1 + (s : ℂ) * I))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hy
    _ ≤ ∫ s in (0 : ℝ)..y, s ^ 2 / 2 :=
      intervalIntegral.integral_mono_on hy (hcont2.norm.intervalIntegrable 0 y)
        (((continuous_pow 2).div_const 2).intervalIntegrable 0 y) (fun s hs ↦ by
          rw [norm_mul, norm_I, one_mul]
          exact hb1 s hs.1)
    _ = y ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; ring

/-- Second-order complex exponential remainder bound
$\|e^{iy} - (1 + iy - y^2 / 2)\| \le |y|^3 / 6$ for all $y \in \mathbb{R}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem norm_cexp_mul_I_sub_quad_le (y : ℝ) :
    ‖cexp ((y : ℂ) * I) - (1 + (y : ℂ) * I - (y : ℂ) ^ 2 / 2)‖ ≤ |y| ^ 3 / 6 := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact norm_cexp_mul_I_sub_quad_le_of_nonneg hy
  · have hny : 0 ≤ -y := by linarith
    rw [abs_of_neg hy]
    have hc2 : (starRingEnd ℂ) 2 = 2 := by simpa using Complex.conj_ofReal 2
    have hconj : starRingEnd ℂ (cexp ((y : ℂ) * I) - (1 + (y : ℂ) * I - (y : ℂ) ^ 2 / 2)) =
        cexp (((-y : ℝ) : ℂ) * I) - (1 + ((-y : ℝ) : ℂ) * I - ((-y : ℝ) : ℂ) ^ 2 / 2) := by
      simp [← Complex.exp_conj, hc2]
    rw [← RCLike.norm_conj, hconj]
    exact norm_cexp_mul_I_sub_quad_le_of_nonneg hny

/-- Real Gaussian quadratic remainder $|e^{-u^2/2} - (1 - u^2/2)| \le u^4 / 8$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem abs_exp_neg_half_sq_sub_quad_le (u : ℝ) :
    |Real.exp (-u ^ 2 / 2) - (1 - u ^ 2 / 2)| ≤ u ^ 4 / 8 := by
  set v : ℝ := u ^ 2 / 2
  have hv : 0 ≤ v := by positivity
  have hlow : 0 ≤ Real.exp (-v) - (1 - v) := by
    have h := Real.add_one_le_exp (-v)
    linarith
  have hd : ∀ s : ℝ, HasDerivAt (fun t : ℝ ↦ 1 - t + t ^ 2 / 2 - Real.exp (-t))
      (Real.exp (-s) - (1 - s)) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ ↦ 1 - t + t ^ 2 / 2) (-1 + s) s := by
      convert (((hasDerivAt_const s (1 : ℝ)).fun_sub (hasDerivAt_id' s)).fun_add
        ((hasDerivAt_pow 2 s).div_const 2)) using 1
      ring
    have h2 : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-Real.exp (-s)) s := by
      convert (hasDerivAt_id' s).fun_neg.exp using 1; ring
    convert h1.fun_sub h2 using 1; ring
  have hcont : Continuous (fun s : ℝ ↦ Real.exp (-s) - (1 - s)) := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    (hcont.intervalIntegrable 0 v)
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..v, (Real.exp (-s) - (1 - s)) :=
    intervalIntegral.integral_nonneg hv fun s _ ↦ by
      have h := Real.add_one_le_exp (-s); linarith
  rw [hftc] at hnonneg
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, neg_zero, Real.exp_zero, sub_self] at hnonneg
  have hval : v ^ 2 / 2 = u ^ 4 / 8 := by simp [v]; ring
  rw [show -u ^ 2 / 2 = -v by simp [v]; ring, abs_of_nonneg hlow]
  linarith

/-! ### Section 2: Single-Summand Characteristic Function and Complex Power Telescoping -/

/-- Characteristic function Taylor bound for a mean-zero, unit-variance $L^3$ random variable:
$\|\varphi_X(u) - (1 - u^2 / 2)\| \le \mathbb{E}|X|^3 |u|^3 / 6$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem norm_charFun_sub_quad_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX3 : MemLp X 3 P) (hmean : ∫ ω, X ω ∂P = 0) (hvar : variance X P = 1) (u : ℝ) :
    ‖charFun (P.map X) u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤
      (∫ ω, |X ω| ^ 3 ∂P) * |u| ^ 3 / 6 := by
  have hX1 : Integrable X P := integrable_of_memLp_three hX3
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) P := integrable_sq_of_memLp_three hX3
  have hX3_int : Integrable (fun ω ↦ |X ω| ^ 3) P := integrable_abs_cube_of_memLp_three hX3
  have hsq1 : ∫ ω, X ω ^ 2 ∂P = 1 :=
    integral_sq_eq_one_of_mean_zero_var_one hX3.aemeasurable hmean hvar
  have hcf : charFun (P.map X) u = ∫ ω, cexp (((u * X ω : ℝ) : ℂ) * I) ∂P := by
    rw [charFun_apply_real, integral_map hX3.aemeasurable (by fun_prop)]
    congr 1 with ω; push_cast; ring_nf
  have hlin : Integrable (fun ω ↦ ((u * X ω : ℝ) : ℂ) * I) P := by
    have : (fun ω ↦ ((u * X ω : ℝ) : ℂ) * I) = fun ω ↦ ((u : ℂ) * I) * (X ω : ℂ) := by
      ext ω; push_cast; ring
    rw [this]; exact hX1.ofReal.const_mul _
  have hsqc : Integrable (fun ω ↦ ((u * X ω : ℝ) : ℂ) ^ 2 / 2) P := by
    have : (fun ω ↦ ((u * X ω : ℝ) : ℂ) ^ 2 / 2) =
        fun ω ↦ ((u : ℂ) ^ 2 / 2) * ((X ω ^ 2 : ℝ) : ℂ) := by
      ext ω; push_cast; ring
    rw [this]; exact hX2.ofReal.const_mul _
  have h1lin : Integrable (fun ω ↦ (1 : ℂ) + ((u * X ω : ℝ) : ℂ) * I) P :=
    (integrable_const (1 : ℂ)).add hlin
  have hquad_int : Integrable
      (fun ω ↦ (1 : ℂ) + ((u * X ω : ℝ) : ℂ) * I - ((u * X ω : ℝ) : ℂ) ^ 2 / 2) P :=
    h1lin.sub hsqc
  have hquad_eq : ∫ ω, ((1 : ℂ) + ((u * X ω : ℝ) : ℂ) * I - ((u * X ω : ℝ) : ℂ) ^ 2 / 2) ∂P =
      1 - (u : ℂ) ^ 2 / 2 := by
    have hlin_eq : ∫ ω, ((u * X ω : ℝ) : ℂ) * I ∂P = 0 := by
      have : (fun ω ↦ ((u * X ω : ℝ) : ℂ) * I) = fun ω ↦ ((u : ℂ) * I) * (X ω : ℂ) := by
        ext ω; push_cast; ring
      rw [this, integral_const_mul, integral_complex_ofReal, hmean, ofReal_zero, mul_zero]
    have hsq_eq : ∫ ω, ((u * X ω : ℝ) : ℂ) ^ 2 / 2 ∂P = (u : ℂ) ^ 2 / 2 := by
      have : (fun ω ↦ ((u * X ω : ℝ) : ℂ) ^ 2 / 2) =
          fun ω ↦ ((u : ℂ) ^ 2 / 2) * ((X ω ^ 2 : ℝ) : ℂ) := by
        ext ω; push_cast; ring
      rw [this, integral_const_mul, integral_complex_ofReal, hsq1, ofReal_one, mul_one]
    have hsub := integral_sub h1lin hsqc
    have hadd := integral_add (integrable_const (1 : ℂ)) hlin
    simp only [integral_const, probReal_univ, one_smul, hlin_eq, add_zero, hsq_eq] at hsub hadd
    rw [hsub, hadd]
  have hexp_int : Integrable (fun ω ↦ cexp (((u * X ω : ℝ) : ℂ) * I)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_
      (Filter.Eventually.of_forall fun ω ↦ by rw [norm_exp_ofReal_mul_I])
    have hcont : Continuous (fun x : ℝ ↦ cexp (((u * x : ℝ) : ℂ) * I)) := by fun_prop
    exact (hcont.measurable.comp_aemeasurable hX3.aemeasurable).aestronglyMeasurable
  rw [hcf, ← hquad_eq, ← integral_sub hexp_int hquad_int]
  refine (norm_integral_le_of_norm_le ((hX3_int.const_mul (|u| ^ 3 / 6))) ?_).trans_eq ?_
  · exact Filter.Eventually.of_forall fun ω ↦ by
      refine (norm_cexp_mul_I_sub_quad_le (u * X ω)).trans_eq ?_
      rw [abs_mul, mul_pow]; ring
  · rw [integral_const_mul]; ring

/-- Complex power telescoping bound $\|z^n - w^n\| \le n M^{n-1} \|z - w\|$ whenever
$\|z\|, \|w\| \le M$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem norm_pow_sub_pow_le (z w : ℂ) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖z ^ n - w ^ n‖ ≤ n * M ^ (n - 1) * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases k with _ | m
    · simp
    · have hid : z ^ (m + 2) - w ^ (m + 2) =
          z * (z ^ (m + 1) - w ^ (m + 1)) + (z - w) * w ^ (m + 1) := by ring
      rw [hid]
      calc
        ‖z * (z ^ (m + 1) - w ^ (m + 1)) + (z - w) * w ^ (m + 1)‖
            ≤ ‖z‖ * ‖z ^ (m + 1) - w ^ (m + 1)‖ + ‖z - w‖ * ‖w‖ ^ (m + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
        _ ≤ M * ((m + 1 : ℕ) * M ^ m * ‖z - w‖) + ‖z - w‖ * M ^ (m + 1) := by
          have ih' : ‖z ^ (m + 1) - w ^ (m + 1)‖ ≤ (m + 1 : ℕ) * M ^ m * ‖z - w‖ := by
            simpa using ih
          have h1 : ‖z‖ * ‖z ^ (m + 1) - w ^ (m + 1)‖ ≤
              M * ((m + 1 : ℕ) * M ^ m * ‖z - w‖) :=
            mul_le_mul hz ih' (norm_nonneg _) hM
          have h2 : ‖z - w‖ * ‖w‖ ^ (m + 1) ≤ ‖z - w‖ * M ^ (m + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw _) (norm_nonneg _)
          linarith
        _ = (m + 2 : ℕ) * M ^ (m + 1) * ‖z - w‖ := by push_cast; ring

/-! ### Section 3: Half-Line Gaussian Moments and Integrated Characteristic Function Bound -/

/-- Half-line second Gaussian moment
$\int_0^\infty t^2 e^{-a t^2}\,dt = \frac{\sqrt{\pi}}{4 a \sqrt{a}}$
for $a > 0$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_Ioi_sq_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-a * t ^ 2) = √π / (4 * a * √a) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ -(s / (2 * a)) * Real.exp (-a * s ^ 2))
      (t ^ 2 * Real.exp (-a * t ^ 2) - 1 / (2 * a) * Real.exp (-a * t ^ 2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ ↦ -(s / (2 * a))) (-(1 / (2 * a))) t := by
      convert ((hasDerivAt_id' t).div_const (2 * a)).fun_neg using 1
    have h2 : HasDerivAt (fun s : ℝ ↦ Real.exp (-a * s ^ 2))
        (Real.exp (-a * t ^ 2) * (-a * (2 * t))) t := by
      have hp : HasDerivAt (fun s : ℝ ↦ -a * s ^ 2) (-a * (2 * t)) t := by
        convert (hasDerivAt_pow 2 t).const_mul (-a) using 1; ring
      exact hp.exp
    convert h1.fun_mul h2 using 1
    field_simp; ring
  have htend : Tendsto (fun t : ℝ ↦ -(t / (2 * a)) * Real.exp (-a * t ^ 2)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ ↦ t ^ (1 : ℝ) * Real.exp (-a * t ^ 2)) atTop (𝓝 0) :=
      (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha 1).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp <| tendsto_id.const_mul_atTop_of_neg (by norm_num))
    have h1 := h0.const_mul (-(1 / (2 * a)))
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t _
    rw [Real.rpow_one]; ring
  have hint_sq : IntegrableOn (fun t : ℝ ↦ t ^ 2 * Real.exp (-a * t ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq ha (s := 2) (by norm_num)).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only; rw [Real.rpow_two]
  have hint_0 : IntegrableOn (fun t : ℝ ↦ 1 / (2 * a) * Real.exp (-a * t ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq ha).const_mul _).integrableOn
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ ↦ hd t) (hint_sq.sub hint_0) htend
  simp only [zero_div, neg_zero, zero_mul, sub_zero] at hftc
  rw [integral_sub hint_sq hint_0, integral_const_mul, integral_gaussian_Ioi a] at hftc
  have hval : 1 / (2 * a) * (√(π / a) / 2) = √π / (4 * a * √a) := by
    rw [Real.sqrt_div Real.pi_pos.le]
    field_simp; ring
  linarith

/-- Half-line third Gaussian moment $\int_0^\infty t^3 e^{-a t^2}\,dt = \frac{1}{2 a^2}$
for $a > 0$ (Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_Ioi_cube_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ 3 * Real.exp (-a * t ^ 2) = 1 / (2 * a ^ 2) := by
  have hd : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ -((1 + a * s ^ 2) / (2 * a ^ 2)) * Real.exp (-a * s ^ 2))
        (t ^ 3 * Real.exp (-a * t ^ 2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ ↦ -((1 + a * s ^ 2) / (2 * a ^ 2)))
        (-(t / a)) t := by
      have hp : HasDerivAt (fun s : ℝ ↦ 1 + a * s ^ 2) (2 * a * t) t := by
        convert ((hasDerivAt_pow 2 t).const_mul a).const_add 1 using 1; ring
      convert (hp.div_const (2 * a ^ 2)).fun_neg using 1
      field_simp
    have h2 : HasDerivAt (fun s : ℝ ↦ Real.exp (-a * s ^ 2))
        (Real.exp (-a * t ^ 2) * (-2 * a * t)) t := by
      have hp : HasDerivAt (fun s : ℝ ↦ -a * s ^ 2) (-2 * a * t) t := by
        convert (hasDerivAt_pow 2 t).const_mul (-a) using 1; ring
      exact hp.exp
    convert h1.fun_mul h2 using 1
    field_simp; ring
  have htend : Tendsto
      (fun s : ℝ ↦ -((1 + a * s ^ 2) / (2 * a ^ 2)) * Real.exp (-a * s ^ 2)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ ↦ Real.exp (-a * s ^ 2)) atTop (𝓝 0) :=
      (exp_neg_mul_sq_isLittleO_exp_neg ha).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    have h2 : Tendsto (fun s : ℝ ↦ s ^ (2 : ℝ) * Real.exp (-a * s ^ 2)) atTop (𝓝 0) :=
      (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha 2).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp <| tendsto_id.const_mul_atTop_of_neg (by norm_num))
    have hsum := (h0.const_mul (-1 / (2 * a ^ 2))).add (h2.const_mul (-1 / (2 * a)))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s _
    rw [Real.rpow_two]; field_simp; ring
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ 3 * Real.exp (-a * t ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq ha (s := 3) (by norm_num)).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only; norm_cast
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ ↦ hd t) hint htend
  rw [hftc]
  simp

/-- Integrated characteristic-function difference bound in the small-$\beta$ regime
($\beta = \rho / \sqrt{n} < 3 / 10$, $T = \frac{7}{5\beta}$, $a = \frac{11}{45}$):
$\int_{(0, T]} (1 - t/T) \frac{\|\varphi_{W_n}(t) - e^{-t^2/2}\|}{t}\,dt \le
\beta \left(\frac{\sqrt{\pi}}{24 a \sqrt{a}} + \frac{3}{160 a^2}\right)$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_charFun_standardizedSum_diff_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {n : ℕ} (hn : 0 < n)
    (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX3 : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hvar : variance (X 0) P = 1)
    (hbeta : (∫ ω, |X 0 ω| ^ 3 ∂P) / √n < 3 / 10) :
    let W : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / √n
    let β : ℝ := (∫ ω, |X 0 ω| ^ 3 ∂P) / √n
    let T : ℝ := 7 / (5 * β)
    let a : ℝ := 11 / 45
    ∫ t in Ioc 0 T, (1 - t / T) * (‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) ≤
      β * (√π / (24 * a * √a) + 3 / (160 * a ^ 2)) := by
  intro W β T a
  set ρ : ℝ := ∫ ω, |X 0 ω| ^ 3 ∂P
  have hρ1 : 1 ≤ ρ := one_le_integral_abs_cube hX3 hmean hvar
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqn_pos : 0 < √n := Real.sqrt_pos.mpr hn_pos
  have hβ_pos : 0 < β := div_pos (by linarith) hsqn_pos
  have hT_pos : 0 < T := by positivity
  have hn12 : 12 ≤ n := by
    have hsqn : 10 / 3 < √n := by
      have : 1 / √n ≤ β := div_le_div_of_nonneg_right hρ1 hsqn_pos.le
      have hlt : 1 / √n < 3 / 10 := this.trans_lt hbeta
      rw [div_lt_div_iff₀ hsqn_pos (by norm_num)] at hlt
      linarith
    have hn_gt : (10 / 3 : ℝ) ^ 2 < n := by
      calc
        (10 / 3 : ℝ) ^ 2 < (√n) ^ 2 := sq_lt_sq' (by linarith) hsqn
        _ = n := Real.sq_sqrt hn_pos.le
    have hn_nat : 11 < n := by
      by_contra! hle
      have : (n : ℝ) ≤ 11 := Nat.cast_le.mpr hle
      linarith
    omega
  have ha_pos : 0 < a := by norm_num [a]
  have hWeq : W = fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω := by
    ext ω; simp [W, div_eq_inv_mul]
  have hpt : ∀ t ∈ Ioc 0 T,
      (1 - t / T) * (‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) ≤
        β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htT : t ≤ T := ht.2
    set u : ℝ := t / √n
    have hu_nonneg : 0 ≤ u := div_nonneg ht0.le hsqn_pos.le
    have htβ : t * β ≤ 7 / 5 := by
      have : t * (5 * β) ≤ 7 := (le_div_iff₀ (by positivity)).mp htT
      linarith
    have hu_le : u ≤ 7 / 5 := by
      have huρ : u * ρ = t * β := by simp [u, β]; ring
      nlinarith
    have hu_sq_lt : u ^ 2 / 2 < 1 := by nlinarith
    let z : ℂ := charFun (P.map (X 0)) u
    let w : ℂ := (Real.exp (-u ^ 2 / 2) : ℂ)
    have hcfW : charFun (P.map W) t = z ^ n := by
      rw [hWeq]
      simpa [z, u, div_eq_inv_mul] using charFun_inv_sqrt_mul_sum hindep hident (n := n) (t := t)
    have hw_pow : cexp (-(t : ℂ) ^ 2 / 2) = w ^ n := by
      have hre : Real.exp (-t ^ 2 / 2) = (Real.exp (-u ^ 2 / 2)) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        have htu : t ^ 2 = n * u ^ 2 := by
          simp [u, div_pow, Real.sq_sqrt hn_pos.le]
          field_simp
        rw [htu]; ring
      have hc : ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) = cexp (-(t : ℂ) ^ 2 / 2) := by
        rw [ofReal_exp]; push_cast; rfl
      rw [← hc, hre, ofReal_pow]
    have hz_diff : ‖z - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ ρ * u ^ 3 / 6 := by
      simpa [z, abs_of_nonneg hu_nonneg] using norm_charFun_sub_quad_le hX3 hmean hvar u
    have hw_diff : ‖w - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ u ^ 4 / 8 := by
      have hcast : w - (1 - (u : ℂ) ^ 2 / 2) =
          ((Real.exp (-u ^ 2 / 2) - (1 - u ^ 2 / 2) : ℝ) : ℂ) := by
        simp [w]
      rw [hcast, norm_real, Real.norm_eq_abs]
      exact abs_exp_neg_half_sq_sub_quad_le u
    have hzw_diff : ‖z - w‖ ≤ ρ * u ^ 3 / 6 + u ^ 4 / 8 := by
      calc
        ‖z - w‖ = ‖(z - (1 - (u : ℂ) ^ 2 / 2)) - (w - (1 - (u : ℂ) ^ 2 / 2))‖ := by ring_nf
        _ ≤ ‖z - (1 - (u : ℂ) ^ 2 / 2)‖ + ‖w - (1 - (u : ℂ) ^ 2 / 2)‖ := norm_sub_le _ _
        _ ≤ ρ * u ^ 3 / 6 + u ^ 4 / 8 := add_le_add hz_diff hw_diff
    let M : ℝ := Real.exp (-(4 / 15) * (t ^ 2 / n))
    have hM_nonneg : 0 ≤ M := (Real.exp_pos _).le
    have hz_norm : ‖z‖ ≤ M := by
      have h1 : ‖(1 : ℂ) - (u : ℂ) ^ 2 / 2‖ = 1 - u ^ 2 / 2 := by
        have hc : (1 : ℂ) - (u : ℂ) ^ 2 / 2 = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [hc, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have h2 : ‖z‖ ≤ 1 - u ^ 2 / 2 + ρ * u ^ 3 / 6 := by
        have := norm_add_le (1 - (u : ℂ) ^ 2 / 2) (z - (1 - (u : ℂ) ^ 2 / 2))
        rw [add_sub_cancel, h1] at this
        linarith
      have h3 : 1 - u ^ 2 / 2 + ρ * u ^ 3 / 6 ≤ 1 - (4 / 15) * (t ^ 2 / n) := by
        have hu2 : u ^ 2 = t ^ 2 / n := by simp [u, div_pow, Real.sq_sqrt hn_pos.le]
        have hu3 : ρ * u ^ 3 = (t ^ 2 / n) * (t * β) := by
          simp only [u, β, div_pow]
          have hsq3 : (√n) ^ 3 = n * √n := by rw [pow_succ, Real.sq_sqrt hn_pos.le]
          rw [hsq3]
          field_simp; ring
        rw [hu2, hu3]
        have ht2n : 0 ≤ t ^ 2 / n := by positivity
        have hmul := mul_le_mul_of_nonneg_left htβ ht2n
        linarith
      have hexp : 1 - (4 / 15) * (t ^ 2 / n) ≤ M := by
        have h := Real.add_one_le_exp (-(4 / 15) * (t ^ 2 / n))
        dsimp only [M]; linarith
      exact (h2.trans h3).trans hexp
    have hw_norm : ‖w‖ ≤ M := by
      simp only [w, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), M]
      apply Real.exp_le_exp.mpr
      have hu2 : u ^ 2 = t ^ 2 / n := by simp [u, div_pow, Real.sq_sqrt hn_pos.le]
      rw [hu2]
      have ht2n : 0 ≤ t ^ 2 / n := by positivity
      linarith
    have hpow := norm_pow_sub_pow_le z w n hM_nonneg hz_norm hw_norm
    have hMpow : M ^ (n - 1) ≤ Real.exp (-a * t ^ 2) := by
      simp only [M, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hn1 : 1 ≤ n := by omega
      have hn_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        simpa using Nat.cast_sub hn1
      rw [hn_sub]
      have hfrac : (11 / 12 : ℝ) ≤ ((n : ℝ) - 1) / n := by
        rw [div_le_div_iff₀ (by norm_num) hn_pos]
        have : (12 : ℝ) ≤ n := Nat.cast_le.mpr hn12
        linarith
      have ha_le : a ≤ ((n : ℝ) - 1) / n * (4 / 15) := by
        simp only [a]; linarith
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      have hmul := mul_le_mul_of_nonneg_right ha_le ht2
      have heq : ((n : ℝ) - 1) * (-(4 / 15) * (t ^ 2 / n)) =
          -(((n : ℝ) - 1) / n * (4 / 15) * t ^ 2) := by field_simp
      linarith
    have hdiff_t : ‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t ≤
        β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2)) := by
      rw [hcfW, hw_pow, div_le_iff₀ ht0]
      have hstep1 : ‖z ^ n - w ^ n‖ ≤ n * Real.exp (-a * t ^ 2) * (ρ * u ^ 3 / 6 + u ^ 4 / 8) := by
        calc
          ‖z ^ n - w ^ n‖ ≤ n * M ^ (n - 1) * ‖z - w‖ := hpow
          _ ≤ n * Real.exp (-a * t ^ 2) * (ρ * u ^ 3 / 6 + u ^ 4 / 8) := by
            have h1 : n * M ^ (n - 1) ≤ n * Real.exp (-a * t ^ 2) :=
              mul_le_mul_of_nonneg_left hMpow (Nat.cast_nonneg n)
            exact mul_le_mul h1 hzw_diff (norm_nonneg _) (by positivity)
      have hstep2 : (n : ℝ) * (ρ * u ^ 3 / 6 + u ^ 4 / 8) ≤
          β * (t ^ 3 / 6 + 3 / 80 * t ^ 4) := by
        have ht1 : (n : ℝ) * (ρ * u ^ 3 / 6) = β * (t ^ 3 / 6) := by
          simp only [u, β, ρ, div_pow]
          have hsq3 : (√n) ^ 3 = n * √n := by rw [pow_succ, Real.sq_sqrt hn_pos.le]
          rw [hsq3]
          field_simp
        have ht2 : (n : ℝ) * (u ^ 4 / 8) ≤ β * (3 / 80 * t ^ 4) := by
          have hu4 : (n : ℝ) * (u ^ 4 / 8) = (1 / n) * (t ^ 4 / 8) := by
            simp only [u, div_pow]
            have hsq4 : (√n) ^ 4 = (n : ℝ) ^ 2 := by
              calc (√n) ^ 4 = ((√n) ^ 2) ^ 2 := by ring
                _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hn_pos.le]
            rw [hsq4]
            field_simp
          have h1n : 1 / (n : ℝ) ≤ 3 / 10 * β := by
            have h1 : 1 / (n : ℝ) = (1 / √n) * (1 / √n) := by
              rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hn_pos.le]
            have h2 : 1 / √n ≤ β := div_le_div_of_nonneg_right hρ1 hsqn_pos.le
            have h3 : 1 / √n ≤ 3 / 10 := h2.trans hbeta.le
            rw [h1]
            exact mul_le_mul h3 h2 (by positivity) (by norm_num)
          rw [hu4]
          have ht4 : 0 ≤ t ^ 4 / 8 := by positivity
          have hmul4 := mul_le_mul_of_nonneg_right h1n ht4
          linarith
        linarith
      calc
        ‖z ^ n - w ^ n‖ ≤ Real.exp (-a * t ^ 2) * ((n : ℝ) * (ρ * u ^ 3 / 6 + u ^ 4 / 8)) := by
          linarith
        _ ≤ Real.exp (-a * t ^ 2) * (β * (t ^ 3 / 6 + 3 / 80 * t ^ 4)) :=
          mul_le_mul_of_nonneg_left hstep2 (Real.exp_pos _).le
        _ = β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2)) * t := by ring
    have hw_le1 : 1 - t / T ≤ 1 := by
      have : 0 ≤ t / T := div_nonneg ht0.le hT_pos.le
      linarith
    calc
      (1 - t / T) * (‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)
          ≤ 1 * (β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2))) :=
        mul_le_mul hw_le1 hdiff_t (by positivity) (by positivity)
      _ = β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2)) := one_mul _
  have hint_g2 : IntegrableOn (fun t : ℝ ↦ t ^ 2 * Real.exp (-a * t ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq ha_pos (s := 2) (by norm_num)).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only; rw [Real.rpow_two]
  have hint_g3 : IntegrableOn (fun t : ℝ ↦ t ^ 3 * Real.exp (-a * t ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq ha_pos (s := 3) (by norm_num)).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only; norm_cast
  have hint_rhs_Ioi : IntegrableOn
      (fun t : ℝ ↦ β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2))) (Ioi 0) := by
    have heq : (fun t : ℝ ↦ β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2))) =
        fun t : ℝ ↦ (β / 6) * (t ^ 2 * Real.exp (-a * t ^ 2)) +
          (3 * β / 80) * (t ^ 3 * Real.exp (-a * t ^ 2)) := by ext t; ring
    rw [heq]
    exact (hint_g2.const_mul _).add (hint_g3.const_mul _)
  have hint_lhs : IntegrableOn
      (fun t : ℝ ↦ (1 - t / T) * (‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t))
      (Ioc 0 T) := by
    refine (hint_rhs_Ioi.mono_set Ioc_subset_Ioi_self).mono' ?_ ?_
    · have hWm : AEMeasurable W P := by
        rw [hWeq]
        exact (Finset.aemeasurable_fun_sum _ fun k _ ↦ (hident k).aemeasurable_fst).const_mul _
      have hprob : IsProbabilityMeasure (P.map W) :=
        ⟨by rw [Measure.map_apply_of_aemeasurable hWm MeasurableSet.univ, preimage_univ,
              measure_univ]⟩
      have hfin : IsFiniteMeasure (P.map W) :=
        ⟨by rw [hprob.measure_univ]; exact ENNReal.one_lt_top⟩
      have hcont : ContinuousOn
          (fun t : ℝ ↦ (1 - t / T) * (‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t))
          (Ioc 0 T) := by
        refine (continuousOn_const.sub (continuousOn_id.div_const T)).mul ?_
        exact (((@continuous_charFun _ _ _ _ _ _ (P.map W) hfin).sub
          (Complex.continuous_exp.comp
            (((continuous_ofReal.pow 2).neg).div_const 2))).norm.continuousOn).div
          continuousOn_id (fun t ht ↦ ht.1.ne')
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hw_nonneg : 0 ≤ 1 - t / T := by
        have : t / T ≤ 1 := (div_le_one hT_pos).mpr ht.2
        linarith
      rw [Real.norm_of_nonneg (mul_nonneg hw_nonneg (div_nonneg (norm_nonneg _) ht.1.le))]
      exact hpt t ht
  calc
    ∫ t in Ioc 0 T, (1 - t / T) * (‖charFun (P.map W) t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)
        ≤ ∫ t in Ioc 0 T, β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2)) :=
      setIntegral_mono_on hint_lhs (hint_rhs_Ioi.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
    _ ≤ ∫ t in Ioi 0, β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2)) :=
      setIntegral_mono_set hint_rhs_Ioi
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
          positivity)
        (Filter.Eventually.of_forall fun t (ht : t ∈ Ioc 0 T) ↦ ht.1)
    _ = β * (√π / (24 * a * √a) + 3 / (160 * a ^ 2)) := by
      have heq : (fun t : ℝ ↦ β * ((t ^ 2 / 6 + 3 / 80 * t ^ 3) * Real.exp (-a * t ^ 2))) =
          fun t : ℝ ↦ (β / 6) * (t ^ 2 * Real.exp (-a * t ^ 2)) +
            (3 * β / 80) * (t ^ 3 * Real.exp (-a * t ^ 2)) := by ext t; ring
      rw [heq, integral_add (hint_g2.const_mul _) (hint_g3.const_mul _),
        integral_const_mul, integral_const_mul,
        integral_Ioi_sq_mul_exp_neg_mul_sq ha_pos,
        integral_Ioi_cube_mul_exp_neg_mul_sq ha_pos]
      ring

end SteinMethod.BerryEsseen
