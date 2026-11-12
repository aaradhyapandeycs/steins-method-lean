/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.OrnsteinUhlenbeck
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# O-U Uniqueness Auxiliaries & Witnesses (`Formalization.Leftovers.OUUniquenessAux`)

Provides Taylor/Lindeberg/characteristic-function helpers, semigroup moment propagation, and the
Part 1 non-vacuity witnesses (`ouKernel_comp`, `ouKernel_lindeberg_tail`,
`ouKernel_quadratic_domination`) for `Formalization.Leftovers.OUUniqueness` (Remark 3.5, `BL8`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Mean-Value, Taylor, Lindeberg, and Characteristic-Function Helpers -/

namespace OUUniquenessAux

noncomputable def cexpI (θ z : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * (z : ℂ) * Complex.I)

lemma cexpI_eq_ofReal_mul (θ z : ℝ) :
    cexpI θ z = Complex.exp (((θ * z : ℝ) : ℂ) * Complex.I) := by
  simp only [cexpI, Complex.ofReal_mul, mul_assoc]

lemma continuous_cexpI (θ : ℝ) : Continuous (cexpI θ) := by unfold cexpI; fun_prop

lemma norm_cexpI (θ z : ℝ) : ‖cexpI θ z‖ = 1 := by
  rw [cexpI_eq_ofReal_mul, Complex.norm_exp_ofReal_mul_I]

lemma integrable_cexpI (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ) :
    Integrable (cexpI θ) μ :=
  Integrable.of_bound (continuous_cexpI θ).aestronglyMeasurable 1
    (ae_of_all _ fun z ↦ (norm_cexpI θ z).le)

lemma charFun_eq_integral_cexpI (μ : Measure ℝ) (θ : ℝ) :
    charFun μ θ = ∫ z, cexpI θ z ∂μ := charFun_apply_real θ

lemma charFun_stdNormalLaw (ξ : ℝ) :
    charFun stdNormalLaw ξ = Complex.exp (-(((ξ ^ 2 / 2 : ℝ) : ℂ))) := by
  rw [stdNormalLaw, charFun_gaussianReal]; congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]; simp

lemma charFun_bind_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (θ : ℝ) :
    charFun (μ.bind κ) θ = ∫ y, charFun (κ y) θ ∂μ := by
  have hf_int : Integrable (fun p : ℝ × ℝ ↦ cexpI θ p.2) (μ ⊗ₘ κ) :=
    Integrable.of_bound ((continuous_cexpI θ).comp continuous_snd).aestronglyMeasurable 1
      (ae_of_all _ fun p ↦ (norm_cexpI θ p.2).le)
  rw [charFun_eq_integral_cexpI, ← Measure.snd_compProd μ κ, Measure.snd,
    integral_map measurable_snd.aemeasurable (continuous_cexpI θ).aestronglyMeasurable,
    Measure.integral_compProd hf_int]
  simp_rw [← charFun_eq_integral_cexpI]

lemma iAdd {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x ↦ f x + g x) μ := hf.add hg

lemma iSub {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x ↦ f x - g x) μ := hf.sub hg

lemma hasDerivAt_sq_sub (x u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (v - x) ^ 2) (2 * (u - x)) u := by
  have hm : HasDerivAt (fun v : ℝ ↦ (v - x) * (v - x)) (2 * (u - x)) u :=
    (((hasDerivAt_id' u).sub_const x).fun_mul
      ((hasDerivAt_id' u).sub_const x)).congr_deriv (by ring)
  exact (show (fun v : ℝ ↦ (v - x) * (v - x)) = fun v ↦ (v - x) ^ 2 from
    funext fun v ↦ (sq (v - x)).symm) ▸ hm

lemma hasDerivAt_cexp_mul_I (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Complex.exp ((v : ℂ) * Complex.I))
      (Complex.I * Complex.exp ((u : ℂ) * Complex.I)) u := by
  have h1 : HasDerivAt (fun v : ℝ ↦ (v : ℂ) * Complex.I) Complex.I u := by
    simpa using (hasDerivAt_id' u).ofReal_comp.mul_const Complex.I
  simpa [mul_comm] using h1.cexp

lemma norm_sub_le_of_hasDerivAt_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' : ℝ → E} {x y C : ℝ} (hg : ∀ u : ℝ, HasDerivAt g (g' u) u)
    (hC : ∀ u : ℝ, |u - x| ≤ |y - x| → ‖g' u‖ ≤ C) :
    ‖g y - g x‖ ≤ C * |y - x| := by
  set s := Icc (x - |y - x|) (x + |y - x|)
  have hx : x ∈ s := ⟨by linarith [abs_nonneg (y - x)], by linarith [abs_nonneg (y - x)]⟩
  have hy : y ∈ s := ⟨by linarith [neg_abs_le (y - x)], by linarith [le_abs_self (y - x)]⟩
  have h := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ ↦ (hg u).hasDerivWithinAt)
    (fun u hu ↦ hC u (abs_sub_le_iff.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩)) hx hy
  rwa [Real.norm_eq_abs] at h

lemma hasDerivAt_primitive {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun z ↦ ∫ u in (0 : ℝ)..z, f u) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt

lemma abs_primitive_taylor_two_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (x y : ℝ)
    (hM : ∀ u : ℝ, |u - x| ≤ |y - x| → |deriv f u - deriv f x| ≤ M) :
    |(∫ u in (0 : ℝ)..y, f u) - (∫ u in (0 : ℝ)..x, f u) -
        f x * (y - x) - (1 / 2) * deriv f x * (y - x) ^ 2| ≤ M * (y - x) ^ 2 := by
  have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hM x (by simp))
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  set h : ℝ → ℝ := fun u ↦ f u - f x - deriv f x * (u - x)
  have hh_deriv : ∀ u : ℝ, HasDerivAt h (deriv f u - deriv f x) u := fun u ↦
    ((hf_diff u).hasDerivAt.sub_const (f x)).sub
      (by simpa using ((hasDerivAt_id' u).sub_const x).const_mul (deriv f x))
  have hh_le : ∀ u : ℝ, |u - x| ≤ |y - x| → |h u| ≤ M * |y - x| := fun u hu ↦ by
    have h1 := norm_sub_le_of_hasDerivAt_ball (x := x) (y := u) (C := M) hh_deriv
      (fun v hv ↦ by simpa [Real.norm_eq_abs] using hM v (hv.trans hu))
    rw [show h x = 0 by simp [h], sub_zero, Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hu hM_nn)
  set R : ℝ → ℝ := fun u ↦ (∫ v in (0 : ℝ)..u, f v) - (∫ v in (0 : ℝ)..x, f v) -
    f x * (u - x) - (1 / 2) * deriv f x * (u - x) ^ 2
  have hR_deriv : ∀ u : ℝ, HasDerivAt R (h u) u := fun u ↦
    (((hasDerivAt_primitive hf.continuous u).sub_const _).sub
      (by simpa using ((hasDerivAt_id' u).sub_const x).const_mul (f x))).sub
      (((hasDerivAt_sq_sub x u).const_mul ((1 / 2) * deriv f x)).congr_deriv (by ring))
  have hR := norm_sub_le_of_hasDerivAt_ball (x := x) (y := y) (C := M * |y - x|) hR_deriv
    (fun u hu ↦ by simpa [Real.norm_eq_abs] using hh_le u hu)
  rw [show R x = 0 by simp [R], sub_zero, Real.norm_eq_abs] at hR
  exact hR.trans_eq (by rw [mul_assoc, ← sq, sq_abs])

lemma norm_cexp_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  simpa using norm_sub_le_of_hasDerivAt_ball (x := 0) (y := θ) (C := 1) hasDerivAt_cexp_mul_I
    (fun u _ ↦ by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I])

lemma norm_cexpI_sub_le (θ₁ θ₂ y : ℝ) :
    ‖cexpI θ₂ y - cexpI θ₁ y‖ ≤ |θ₂ - θ₁| * |y| := by
  have hm : cexpI θ₂ y =
      cexpI θ₁ y * Complex.exp ((((θ₂ - θ₁) * y : ℝ) : ℂ) * Complex.I) := by
    simp only [cexpI, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub]
    congr 1; ring
  have h : cexpI θ₂ y - cexpI θ₁ y =
      cexpI θ₁ y * (Complex.exp ((((θ₂ - θ₁) * y : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [hm]; ring
  rw [h, norm_mul, norm_cexpI, one_mul]
  exact (norm_cexp_sub_one_le _).trans_eq (abs_mul (θ₂ - θ₁) y)

lemma hasDerivAt_cexpI_comp {g : ℝ → ℝ} {s g' : ℝ}
    (hg : HasDerivAt g g' s) (y : ℝ) :
    HasDerivAt (fun u ↦ cexpI (g u) y)
      (cexpI (g s) y * (Complex.I * ((g' * y : ℝ) : ℂ))) s := by
  have h1 := (hg.mul_const y).ofReal_comp.mul_const Complex.I
  rw [show (fun u ↦ cexpI (g u) y) =
      fun u ↦ Complex.exp (((g u * y : ℝ) : ℂ) * Complex.I) from
    funext fun u ↦ cexpI_eq_ofReal_mul (g u) y]
  exact h1.cexp.congr_deriv (by rw [cexpI_eq_ofReal_mul]; ring)

lemma norm_cexp_taylor_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - (1 + (θ : ℂ) * Complex.I)‖ ≤ θ ^ 2 := by
  set g₁ : ℝ → ℂ := fun u ↦
    Complex.exp ((u : ℂ) * Complex.I) - (1 + (u : ℂ) * Complex.I)
  have hg₁ : ∀ u : ℝ,
      HasDerivAt g₁ (Complex.I * (Complex.exp ((u : ℂ) * Complex.I) - 1)) u := fun u ↦
    ((hasDerivAt_cexp_mul_I u).sub (by
      simpa using ((hasDerivAt_id' u).ofReal_comp.mul_const Complex.I).const_add 1)).congr_deriv
      (by ring)
  have h := norm_sub_le_of_hasDerivAt_ball (x := 0) (y := θ) (C := |θ|) hg₁ fun u hu ↦ by
    rw [norm_mul, Complex.norm_I, one_mul]; exact (norm_cexp_sub_one_le u).trans (by simpa using hu)
  rw [show g₁ 0 = 0 by simp [g₁], sub_zero, sub_zero] at h
  exact h.trans_eq (by rw [← sq, sq_abs])

lemma norm_cexp_taylor_two_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) -
        (1 + (θ : ℂ) * Complex.I - ((θ ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      min (2 * θ ^ 2) (|θ| ^ 3) := by
  set g₂ : ℝ → ℂ := fun u ↦
    Complex.exp ((u : ℂ) * Complex.I) - (1 + (u : ℂ) * Complex.I - ((u ^ 2 / 2 : ℝ) : ℂ))
  change ‖g₂ θ‖ ≤ min (2 * θ ^ 2) (|θ| ^ 3)
  refine le_min ?_ ?_
  · rw [show g₂ θ = (Complex.exp ((θ : ℂ) * Complex.I) - (1 + (θ : ℂ) * Complex.I)) +
        ((θ ^ 2 / 2 : ℝ) : ℂ) by dsimp only [g₂]; ring]
    have hhalf : ‖((θ ^ 2 / 2 : ℝ) : ℂ)‖ = θ ^ 2 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [norm_add_le (Complex.exp ((θ : ℂ) * Complex.I) - (1 + (θ : ℂ) * Complex.I))
      ((θ ^ 2 / 2 : ℝ) : ℂ), norm_cexp_taylor_one_le θ, sq_nonneg θ]
  · have hg₂ : ∀ u : ℝ, HasDerivAt g₂
        (Complex.I * (Complex.exp ((u : ℂ) * Complex.I) -
          (1 + (u : ℂ) * Complex.I))) u := fun u ↦ by
      have h1 : HasDerivAt (fun v : ℝ ↦ (1 : ℂ) + (v : ℂ) * Complex.I) Complex.I u := by
        simpa using ((hasDerivAt_id' u).ofReal_comp.mul_const Complex.I).const_add 1
      have h2r : HasDerivAt (fun v : ℝ ↦ v ^ 2 / 2) u u := by
        simpa only [sub_zero] using
          ((hasDerivAt_sq_sub 0 u).div_const (2 : ℝ)).congr_deriv (by ring)
      refine ((hasDerivAt_cexp_mul_I u).sub (h1.sub h2r.ofReal_comp)).congr_deriv ?_
      calc Complex.I * Complex.exp ((u : ℂ) * Complex.I) - (Complex.I - (u : ℂ))
        _ = Complex.I * (Complex.exp ((u : ℂ) * Complex.I) - 1) -
              (u : ℂ) * (Complex.I * Complex.I) := by rw [Complex.I_mul_I]; ring
        _ = Complex.I * (Complex.exp ((u : ℂ) * Complex.I) -
              (1 + (u : ℂ) * Complex.I)) := by ring
    have h := norm_sub_le_of_hasDerivAt_ball (x := 0) (y := θ) (C := θ ^ 2) hg₂ fun u hu ↦ by
      rw [norm_mul, Complex.norm_I, one_mul, ← sq_abs θ]
      refine (norm_cexp_taylor_one_le u).trans ?_
      rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg u) (by simpa using hu) 2
    rw [show g₂ 0 = 0 by simp [g₂], sub_zero, sub_zero] at h
    exact h.trans_eq (by rw [← sq_abs θ]; ring)

lemma integrable_sub_of_integrable_sq {ν : Measure ℝ} [IsProbabilityMeasure ν] {x : ℝ}
    (hsq : Integrable (fun y : ℝ ↦ (y - x) ^ 2) ν) : Integrable (fun y : ℝ ↦ y - x) ν :=
  ((integrable_const (1 : ℝ)).add hsq).mono'
    (measurable_id.sub measurable_const).aestronglyMeasurable
    (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, Pi.add_apply]; nlinarith [sq_abs (y - x), abs_nonneg (y - x)])

lemma integrable_abs_of_integrable_sq {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hsq : Integrable (fun y : ℝ ↦ y ^ 2) ν) : Integrable (fun y : ℝ ↦ |y|) ν :=
  ((integrable_const (1 : ℝ)).add hsq).mono' continuous_abs.aestronglyMeasurable
    (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, abs_abs, Pi.add_apply]; nlinarith [sq_abs y, abs_nonneg y])

lemma tendsto_div_of_sub_littleO {g : ℝ → ℝ} {c : ℝ}
    (h : Tendsto (fun a : ℝ ↦ (g a - c * a) / a) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun a : ℝ ↦ g a / a) (𝓝[>] 0) (𝓝 c) := by
  have h1 := h.add (tendsto_const_nhds (x := c)); rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha; field_simp [(mem_Ioi.mp ha).ne']; ring

lemma tendsto_remainder_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℝ → Kernel ℝ ℝ} {x : ℝ} (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    (hDiff' : Tendsto (fun a : ℝ ↦ (∫ y, (y - x) ^ 2 ∂K a x) / a) (𝓝[>] 0) (𝓝 2))
    (hLind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂K a x) / a)
        (𝓝[>] 0) (𝓝 0))
    (hInt2_loc : ∀ᶠ a in 𝓝[>] 0, Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x))
    {r : ℝ → ℝ → E} (hr_meas : ∀ᶠ a in 𝓝[>] 0, AEStronglyMeasurable (r a) (K a x))
    {B : ℝ} (_hB_nn : 0 ≤ B)
    (hr_glob : ∀ᶠ a in 𝓝[>] 0, ∀ y : ℝ, ‖r a y‖ ≤ B * (y - x) ^ 2)
    (hr_loc : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ a in 𝓝[>] 0, ∀ y : ℝ, |y - x| ≤ δ → ‖r a y‖ ≤ η * (y - x) ^ 2) :
    Tendsto (fun a : ℝ ↦ a⁻¹ • ∫ y, r a y ∂K a x) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  set η : ℝ := ε / 8; have hη : 0 < η := by positivity
  obtain ⟨δ, hδ_pos, hδ_ev⟩ := hr_loc η hη
  have htail_lim : Tendsto
      (fun a : ℝ ↦ (B + 1) * ((∫ y in {y : ℝ | δ < |y - x|}, (y - x) ^ 2 ∂K a x) / a))
      (𝓝[>] 0) (𝓝 0) := by simpa using (hLind δ hδ_pos).const_mul (B + 1)
  filter_upwards [self_mem_nhdsWithin, hInt2_loc, hr_meas, hr_glob, hδ_ev,
    (Metric.tendsto_nhds.mp hDiff') 1 zero_lt_one,
    (Metric.tendsto_nhds.mp htail_lim) (ε / 2) (half_pos hε)] with
    a ha hInt2 hmeas hglob hloc ha_d2 ha_tail
  have ha_pos : 0 < a := mem_Ioi.mp ha; have := hMarkov a ha_pos
  have hms : MeasurableSet {y : ℝ | δ < |y - x|} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
  have hind_int := (hInt2.const_mul (B + 1)).integrableOn.integrable_indicator hms
  have hint_le : ‖∫ y, r a y ∂K a x‖ ≤ η * (∫ y, (y - x) ^ 2 ∂K a x) +
      (B + 1) * ∫ y in {y : ℝ | δ < |y - x|}, (y - x) ^ 2 ∂K a x := by
    refine (norm_integral_le_of_norm_le (iAdd (hInt2.const_mul η) hind_int)
      (ae_of_all _ fun y ↦ ?_)).trans_eq ?_
    · by_cases hy : y ∈ {y' : ℝ | δ < |y' - x|}
      · rw [Set.indicator_of_mem hy]
        nlinarith [hglob y, sq_nonneg (y - x), mul_nonneg hη.le (sq_nonneg (y - x))]
      · rw [Set.indicator_of_notMem hy, add_zero]; exact hloc y (not_lt.mp hy)
    · rw [integral_add (hInt2.const_mul η) hind_int, integral_const_mul,
        integral_indicator hms, integral_const_mul]
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha_pos, inv_mul_eq_div]
  rw [Real.dist_eq] at ha_d2 ha_tail
  have hdiv := div_le_div_of_nonneg_right hint_le ha_pos.le
  rw [add_div, mul_div_assoc, mul_div_assoc] at hdiv
  have hfirst : η * ((∫ y, (y - x) ^ 2 ∂K a x) / a) < 3 * η := by
    nlinarith [(abs_lt.mp ha_d2).2]
  linarith [(abs_lt.mp ha_tail).2, show 3 * η = 3 * ε / 8 by dsimp [η]; ring]

lemma coe_ouVar_local {a : ℝ} (ha : 0 < a) :
    ((Real.toNNReal (1 - Real.exp (-2 * a)) : ℝ≥0) : ℝ) = 1 - Real.exp (-2 * a) :=
  Real.coe_toNNReal _ (by linarith [Real.exp_lt_one_iff.mpr (by linarith : -2 * a < 0)])

lemma charFun_ouKernel {a : ℝ} (ha : 0 < a) (x ξ : ℝ) :
    charFun (ouKernel a x) ξ =
      Complex.exp ((((ξ * (Real.exp (-a) * x) : ℝ) : ℂ) * Complex.I) -
        ((((1 - Real.exp (-2 * a)) * ξ ^ 2 / 2 : ℝ) : ℂ))) := by
  rw [ouKernel_of_pos ha x, charFun_gaussianReal, coe_ouVar_local ha]; congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]

abbrev QuadDom (K : ℝ → Kernel ℝ ℝ) (a₀ C : ℝ) : Prop :=
  ∀ a ∈ Ioo 0 a₀, ∀ x : ℝ, Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x) ∧
    |∫ y, (y - x) ∂K a x| ≤ C * a * (1 + |x|) ∧
    (∫ y, (y - x) ^ 2 ∂K a x) ≤ C * a * (1 + x ^ 2)

lemma hasDerivWithinAt_Ici_of_tendsto_right {g : ℝ → ℂ} {s : ℝ} {L : ℂ}
    (h : Tendsto (fun a : ℝ ↦ (g (s + a) - g s) / (a : ℂ)) (𝓝[>] 0) (𝓝 L)) :
    HasDerivWithinAt g L (Ici s) s := by
  refine HasDerivWithinAt.Ici_of_Ioi ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mpr ?_)
  have ht : Tendsto (fun u : ℝ ↦ u - s) (𝓝 s) (𝓝 0) := by
    simpa only [sub_self] using (by fun_prop : Continuous fun u : ℝ ↦ u - s).tendsto s
  have hsub : Tendsto (fun u : ℝ ↦ u - s) (𝓝[>] s) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (ht.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun u (hu : s < u) ↦ sub_pos.mpr hu)
  refine (h.comp hsub).congr fun u ↦ ?_
  dsimp only [Function.comp_apply]
  rw [add_sub_cancel, slope_def_module]
  simp [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

lemma uniform_sq_bound_of_semigroup {K : ℝ → Kernel ℝ ℝ}
    (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C) (hDom : QuadDom K a₀ C)
    (hSemi : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s))
    {t : ℝ} (_ht : 0 < t) (x : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Ioc 0 t,
      Integrable (fun y : ℝ ↦ y ^ 2) (K s x) ∧ (∫ y, y ^ 2 ∂K s x) ≤ M := by
  set A : ℝ := 2 + 2 * C * a₀; set B : ℝ := 2 * C * a₀
  have hA : 2 ≤ A := by linarith [mul_nonneg hC ha₀.le]
  have hB : 0 ≤ B := by positivity
  have hone : ∀ a ∈ Ioo 0 a₀, ∀ y : ℝ,
      Integrable (fun z : ℝ ↦ z ^ 2) (K a y) ∧ (∫ z, z ^ 2 ∂K a y) ≤ A * y ^ 2 + B ∧
        (∫⁻ z, ENNReal.ofReal (z ^ 2) ∂K a y) ≤
          ENNReal.ofReal A * ENNReal.ofReal (y ^ 2) + ENNReal.ofReal B := by
    intro a ha y; have := hMarkov a ha.1; obtain ⟨hInt_sub, -, hSq_sub⟩ := hDom a ha y
    have hInt_z2 : Integrable (fun z : ℝ ↦ z ^ 2) (K a y) :=
      (iAdd (integrable_const (2 * y ^ 2)) (hInt_sub.const_mul 2)).mono'
        (continuous_pow 2).aestronglyMeasurable (ae_of_all _ fun z ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]; nlinarith [sq_nonneg (2 * y - z)])
    have hle_int : (∫ z, z ^ 2 ∂K a y) ≤ A * y ^ 2 + B := by
      have hm := integral_mono hInt_z2 (iAdd (integrable_const (2 * y ^ 2)) (hInt_sub.const_mul 2))
        fun z ↦ by dsimp only; nlinarith [sq_nonneg (2 * y - z)]
      rw [integral_add (integrable_const (2 * y ^ 2)) (hInt_sub.const_mul 2), integral_const,
        probReal_univ, one_smul, integral_const_mul] at hm
      dsimp only [A, B]; nlinarith [sq_nonneg y, mul_le_mul_of_nonneg_left ha.2.le hC]
    refine ⟨hInt_z2, hle_int, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hInt_z2 (ae_of_all _ fun z ↦ sq_nonneg z),
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) hB]
    exact ENNReal.ofReal_le_ofReal hle_int
  set δ : ℝ := a₀ / 2
  have hδ_pos : 0 < δ := half_pos ha₀
  have hδ_lt : δ < a₀ := half_lt_self ha₀
  have hind : ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Ioc 0 (((n : ℝ) + 1) * δ),
      Integrable (fun y : ℝ ↦ y ^ 2) (K s x) ∧ (∫ y, y ^ 2 ∂K s x) ≤ M := by
    intro n; induction n with
    | zero =>
      refine ⟨A * x ^ 2 + B, by positivity, fun s hs ↦ ?_⟩
      have hs_lt : s < a₀ := by
        have h2 := hs.2; rw [Nat.cast_zero, zero_add, one_mul] at h2; linarith
      exact ⟨(hone s ⟨hs.1, hs_lt⟩ x).1, (hone s ⟨hs.1, hs_lt⟩ x).2.1⟩
    | succ n ih =>
      obtain ⟨M, hM_nn, hM⟩ := ih; refine ⟨A * M + B, by positivity, fun s hs ↦ ?_⟩
      by_cases hle : s ≤ ((n : ℝ) + 1) * δ
      · obtain ⟨hI, hL⟩ := hM s ⟨hs.1, hle⟩; exact ⟨hI, hL.trans (by nlinarith)⟩
      · set u : ℝ := ((n : ℝ) + 1) * δ; have hu_pos : 0 < u := by positivity
        set a : ℝ := s - u
        have ha_le : a ≤ δ := by have hs2 := hs.2; push_cast at hs2; dsimp only [a, u]; linarith
        have ha_Ioo : a ∈ Ioo 0 a₀ :=
          ⟨sub_pos.mpr (not_le.mp hle), lt_of_le_of_lt ha_le hδ_lt⟩
        have := hMarkov u hu_pos; have := hMarkov a ha_Ioo.1
        obtain ⟨hIu, hLu⟩ := hM u ⟨hu_pos, le_rfl⟩
        have hlint_le : (∫⁻ z, ENNReal.ofReal (z ^ 2) ∂K s x) ≤
            ENNReal.ofReal (A * M + B) := by
          rw [show s = u + a by ring, hSemi u hu_pos a ha_Ioo.1, Kernel.comp_apply,
            Measure.lintegral_bind (Kernel.measurable _).aemeasurable (by fun_prop)]
          calc (∫⁻ y, (∫⁻ z, ENNReal.ofReal (z ^ 2) ∂K a y) ∂K u x)
            _ ≤ ∫⁻ y, (ENNReal.ofReal A * ENNReal.ofReal (y ^ 2) +
                  ENNReal.ofReal B) ∂K u x := lintegral_mono fun y ↦ (hone a ha_Ioo y).2.2
            _ = ENNReal.ofReal A * (∫⁻ y, ENNReal.ofReal (y ^ 2) ∂K u x) +
                  ENNReal.ofReal B := by
                rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (by fun_prop),
                  lintegral_const, measure_univ, mul_one]
            _ ≤ ENNReal.ofReal A * ENNReal.ofReal M + ENNReal.ofReal B := by
                rw [← ofReal_integral_eq_lintegral_ofReal hIu (ae_of_all _ fun y ↦ sq_nonneg y)]
                gcongr
            _ = ENNReal.ofReal (A * M + B) := by
                rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) hB]
        have hInt_s : Integrable (fun z : ℝ ↦ z ^ 2) (K s x) :=
          ⟨(continuous_pow 2).aestronglyMeasurable, by
            rw [HasFiniteIntegral, lintegral_congr fun z ↦ Real.enorm_eq_ofReal (sq_nonneg z)]
            exact hlint_le.trans_lt ENNReal.ofReal_lt_top⟩
        refine ⟨hInt_s, (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ?_⟩
        rwa [ofReal_integral_eq_lintegral_ofReal hInt_s (ae_of_all _ fun z ↦ sq_nonneg z)]
  obtain ⟨M, hM_nn, hM⟩ := hind (Nat.floor (t / δ))
  exact ⟨M, hM_nn, fun s hs ↦ hM s ⟨hs.1, hs.2.trans ((div_lt_iff₀ hδ_pos).mp
    (Nat.lt_floor_add_one (t / δ))).le⟩⟩

end OUUniquenessAux

/-! ### Section 2: Non-Vacuity Witnesses for `ouKernel` (Part 1) -/

open OUUniquenessAux

/-- Chapman–Kolmogorov semigroup identity for `ouKernel` on `(0, ∞)`
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem ouKernel_comp {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ouKernel (s + t) = Kernel.comp (ouKernel t) (ouKernel s) := by
  refine Kernel.ext fun x ↦ Measure.ext_of_charFun (funext fun ξ ↦ ?_)
  rw [Kernel.comp_apply, charFun_bind_eq (ouKernel s x) (ouKernel t) ξ]
  have hinner : ∀ y : ℝ, charFun (ouKernel t y) ξ =
      Complex.exp (-((((1 - Real.exp (-2 * t)) * ξ ^ 2 / 2 : ℝ) : ℂ))) *
        cexpI (Real.exp (-t) * ξ) y := fun y ↦ by
    rw [charFun_ouKernel ht y ξ, cexpI, ← Complex.exp_add]
    congr 1; simp only [Complex.ofReal_mul]; ring
  simp_rw [hinner, integral_const_mul, ← charFun_eq_integral_cexpI,
    charFun_ouKernel hs x (Real.exp (-t) * ξ), charFun_ouKernel (add_pos hs ht) x ξ,
    ← Complex.exp_add]
  congr 1
  have he2t : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by rw [sq, ← Real.exp_add]; congr 1; ring
  have he2st : Real.exp (-2 * (s + t)) = Real.exp (-2 * s) * Real.exp (-2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hre : (1 - Real.exp (-2 * (s + t))) * ξ ^ 2 / 2 =
      (1 - Real.exp (-2 * t)) * ξ ^ 2 / 2 +
        (1 - Real.exp (-2 * s)) * (Real.exp (-t) * ξ) ^ 2 / 2 := by rw [mul_pow, he2t, he2st]; ring
  have him : (Real.exp (-t) * ξ) * (Real.exp (-s) * x) = ξ * (Real.exp (-(s + t)) * x) := by
    rw [neg_add, Real.exp_add]; ring
  rw [him, hre, Complex.ofReal_add]; ring

/-- Lindeberg second-moment tail condition for `ouKernel` as $a \to 0^+$
(Remark 3.5, `SteinIntro.tex:1014-1018`). -/
theorem ouKernel_lindeberg_tail (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂ouKernel a x) / a)
      (𝓝[>] 0) (𝓝 0) := by
  have hZ4 : Integrable (fun z : ℝ ↦ z ^ 4) stdNormalLaw :=
    integrable_pow_four (by rw [stdNormalLaw]; exact memLp_id_gaussianReal 4)
  set cZ : ℝ := ∫ z, z ^ 4 ∂stdNormalLaw
  have hcZ_nn : 0 ≤ cZ := integral_nonneg fun _ ↦ by positivity
  have hc : Continuous (fun a : ℝ ↦ ((8 * x ^ 4 + 32 * cZ) / ε ^ 2) * a) := by fun_prop
  have hU : Tendsto (fun a : ℝ ↦ ((8 * x ^ 4 + 32 * cZ) / ε ^ 2) * a)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (hc.continuousWithinAt (x := 0) (s := Ioi 0)).tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact div_nonneg (setIntegral_nonneg
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
      fun _ _ ↦ sq_nonneg _) (mem_Ioi.mp ha).le
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with a ha
    have ha_pos : 0 < a := ha.1
    set m : ℝ := (Real.exp (-a) - 1) * x
    have hv_pos : 0 < 1 - Real.exp (-2 * a) := by
      linarith [Real.exp_lt_one_iff.mpr (by linarith : -2 * a < 0)]
    set s : ℝ := Real.sqrt (1 - Real.exp (-2 * a))
    have hmap_aff : (ouKernel a x).map (· - x) = stdNormalLaw.map (fun z ↦ m + s * z) := by
      calc (ouKernel a x).map (· - x)
        _ = gaussianReal (s * 0 + m) (NNReal.mk (s ^ 2) (sq_nonneg s) * 1) := by
            rw [ouKernel_map_sub_const ha_pos x]; congr 1
            · ring
            · ext; rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one,
                coe_ouVar_local ha_pos, Real.sq_sqrt hv_pos.le]
        _ = ((gaussianReal 0 1).map (s * ·)).map (m + ·) := by
            rw [gaussianReal_map_const_mul, gaussianReal_map_const_add]
        _ = stdNormalLaw.map (fun z ↦ m + s * z) := by
            rw [stdNormalLaw, Measure.map_map (measurable_const_add m) (measurable_const_mul s)]
            rfl
    have hInt4_map : Integrable (fun w : ℝ ↦ w ^ 4) ((ouKernel a x).map (· - x)) :=
      integrable_pow_four (by rw [ouKernel_map_sub_const ha_pos x]; exact memLp_id_gaussianReal 4)
    have hInt4 : Integrable (fun y : ℝ ↦ (y - x) ^ 4) (ouKernel a x) :=
      (integrable_map_measure (continuous_pow 4).aestronglyMeasurable
        (measurable_id.sub measurable_const).aemeasurable).mp hInt4_map
    have hInt2 : Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) :=
      ((integrable_const (1 : ℝ)).add hInt4).mono' (by fun_prop) (ae_of_all _ fun y ↦ by
        rw [Real.norm_eq_abs, Pi.add_apply, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg ((y - x) ^ 2 - 1)])
    have hms : MeasurableSet {y : ℝ | ε < |y - x|} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
    have hε2_pos : 0 < ε ^ 2 := pow_pos hε 2
    have hset_le : ε ^ 2 * (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂ouKernel a x) ≤
        ∫ y, (y - x) ^ 4 ∂ouKernel a x := by
      rw [← integral_const_mul, ← integral_indicator hms]
      refine integral_mono ((hInt2.const_mul (ε ^ 2)).integrableOn.integrable_indicator hms) hInt4
        fun y ↦ ?_
      by_cases hy : y ∈ {y' : ℝ | ε < |y' - x|}
      · rw [Set.indicator_of_mem hy]
        have hε2 : ε ^ 2 ≤ (y - x) ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ hε.le (le_of_lt hy) 2
        nlinarith [sq_nonneg (y - x)]
      · rw [Set.indicator_of_notMem hy]; positivity
    have hInt_aff : Integrable (fun z : ℝ ↦ (m + s * z) ^ 4) stdNormalLaw := by
      rw [hmap_aff] at hInt4_map
      exact (integrable_map_measure (continuous_pow 4).aestronglyMeasurable
        (by fun_prop)).mp hInt4_map
    have heq4 : (∫ y, (y - x) ^ 4 ∂ouKernel a x) = ∫ z, (m + s * z) ^ 4 ∂stdNormalLaw := by
      rw [← integral_map (φ := fun y ↦ y - x) (f := fun w : ℝ ↦ w ^ 4)
          (measurable_id.sub measurable_const).aemeasurable
          (continuous_pow 4).aestronglyMeasurable,
        hmap_aff, integral_map (φ := fun z ↦ m + s * z) (f := fun w : ℝ ↦ w ^ 4)
          (by fun_prop) (continuous_pow 4).aestronglyMeasurable]
    have hs4 : s ^ 4 = (1 - Real.exp (-2 * a)) ^ 2 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sq_sqrt hv_pos.le]
    have hpow4_le : (∫ y, (y - x) ^ 4 ∂ouKernel a x) ≤
        8 * m ^ 4 + 8 * (1 - Real.exp (-2 * a)) ^ 2 * cZ := by
      rw [heq4]
      have hb_int := iAdd (integrable_const (8 * m ^ 4))
        (hZ4.const_mul (8 * (1 - Real.exp (-2 * a)) ^ 2))
      refine (integral_mono hInt_aff hb_int fun z ↦ ?_).trans_eq ?_
      · have h8 : (m + s * z) ^ 4 ≤ 8 * m ^ 4 + 8 * (s * z) ^ 4 := by
          have hid : 8 * m ^ 4 + 8 * (s * z) ^ 4 - (m + s * z) ^ 4 =
              (2 * (m ^ 2 + (s * z) ^ 2) + (m + s * z) ^ 2) * (m - s * z) ^ 2 +
                4 * (m ^ 2 - (s * z) ^ 2) ^ 2 := by ring
          linarith [show 0 ≤ (2 * (m ^ 2 + (s * z) ^ 2) + (m + s * z) ^ 2) *
            (m - s * z) ^ 2 + 4 * (m ^ 2 - (s * z) ^ 2) ^ 2 by positivity]
        exact h8.trans_eq (by rw [mul_pow s z, hs4]; ring)
      · rw [integral_add (integrable_const (8 * m ^ 4))
            (hZ4.const_mul (8 * (1 - Real.exp (-2 * a)) ^ 2)),
          integral_const, probReal_univ, one_smul, integral_const_mul]
    have hm_le : m ^ 4 ≤ a ^ 2 * x ^ 4 := by
      have h1 : |Real.exp (-a) - 1| ≤ a := by
        rw [abs_sub_comm,
          abs_of_nonneg (by linarith [Real.exp_lt_one_iff.mpr (by linarith : -a < 0)])]
        linarith [Real.add_one_le_exp (-a)]
      have h2 : (Real.exp (-a) - 1) ^ 4 ≤ a ^ 4 := by
        rw [show (Real.exp (-a) - 1) ^ 4 = (|Real.exp (-a) - 1| ^ 2) ^ 2 by rw [sq_abs]; ring,
          show (|Real.exp (-a) - 1| ^ 2) ^ 2 = |Real.exp (-a) - 1| ^ 4 by ring]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 4
      have ha42 : a ^ 4 ≤ a ^ 2 := by
        nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha.2.le), ha.1, ha.2]
      dsimp only [m]; rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (h2.trans ha42) (by positivity)
    have hv_le : (1 - Real.exp (-2 * a)) ^ 2 ≤ 4 * a ^ 2 := by
      nlinarith [hv_pos, Real.add_one_le_exp (-2 * a)]
    calc (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂ouKernel a x) / a
      _ ≤ ((∫ y, (y - x) ^ 4 ∂ouKernel a x) / ε ^ 2) / a := by
          gcongr; rwa [le_div_iff₀' hε2_pos]
      _ ≤ ((8 * (a ^ 2 * x ^ 4) + 8 * (4 * a ^ 2) * cZ) / ε ^ 2) / a := by
          gcongr; linarith [mul_le_mul_of_nonneg_right hv_le hcZ_nn]
      _ = ((8 * x ^ 4 + 32 * cZ) / ε ^ 2) * a := by field_simp [ha_pos.ne', hε2_pos.ne']; ring

/-- Small-time quadratic moment domination for `ouKernel` on `(0, 1)` with constant `2`
(Remark 3.5, `SteinIntro.tex:1014-1018`). -/
theorem ouKernel_quadratic_domination :
    ∀ a ∈ Ioo (0 : ℝ) 1, ∀ x : ℝ,
      Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) ∧
        |∫ y, (y - x) ∂ouKernel a x| ≤ 2 * a * (1 + |x|) ∧
        (∫ y, (y - x) ^ 2 ∂ouKernel a x) ≤ 2 * a * (1 + x ^ 2) := by
  intro a ha x; have ha_pos : 0 < a := ha.1
  have hInt2 : Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) := by
    have hmap : MemLp (id : ℝ → ℝ) 2 ((ouKernel a x).map (· - x)) := by
      rw [ouKernel_map_sub_const ha_pos x]; exact memLp_id_gaussianReal 2
    exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
      (measurable_id.sub measurable_const).aemeasurable).mp hmap.integrable_sq
  have hexp1 : 0 ≤ 1 - Real.exp (-a) ∧ 1 - Real.exp (-a) ≤ a :=
    ⟨by linarith [Real.exp_lt_one_iff.mpr (by linarith : -a < 0)],
      by linarith [Real.add_one_le_exp (-a)]⟩
  refine ⟨hInt2, ?_, ?_⟩
  · rw [integral_sub_ouKernel ha_pos x, abs_mul,
      show |Real.exp (-a) - 1| = 1 - Real.exp (-a) by rw [abs_sub_comm, abs_of_nonneg hexp1.1]]
    nlinarith [abs_nonneg x]
  · rw [integral_sq_sub_ouKernel ha_pos x]
    have hsq : (Real.exp (-a) - 1) ^ 2 ≤ 2 * a := by
      rw [show (Real.exp (-a) - 1) ^ 2 = (1 - Real.exp (-a)) ^ 2 by ring]
      nlinarith [hexp1.1, hexp1.2, ha.2]
    nlinarith [Real.add_one_le_exp (-2 * a), sq_nonneg x]

end SteinMethod
