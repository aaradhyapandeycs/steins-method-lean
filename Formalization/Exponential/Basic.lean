/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Basic Properties & Non-Vacuity Witnesses (`Formalization.Exponential.Basic`)

Foundational measure-theoretic, moment, and integration-by-parts lemmas for `expLaw`, `stdExpLaw`,
and `shiftedGeomLaw`, together with:
* Non-vacuity witnesses for the Section 5 definitions (`isProbabilityMeasure_stdExpLaw`,
  `isProbabilityMeasure_shiftedGeomLaw`, `shiftedGeomLaw_singleton_of_pos`, and
  `isEquilibrium_stdExpLaw : IsEquilibrium stdExpLaw id stdExpLaw id`);
* **Example 5.4 ceiling claim** (`ex5_4_ceil_corrected`, `SteinIntro.tex:2885-2886`,
  `ISSUE-TYPO-5.4`): for $\lambda > 0$ and $Z \sim \mathrm{Exp}(\lambda)$,
  $\lceil Z \rceil \sim \mathrm{Ge}(1 - e^{-\lambda})$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Exponential Law Density, Tail Probabilities, and Moments -/

instance isProbabilityMeasure_stdExpLaw : IsProbabilityMeasure stdExpLaw :=
  isProbabilityMeasure_expMeasure zero_lt_one

theorem expLaw_eq_withDensity (r : ℝ) :
    expLaw r = volume.withDensity (exponentialPDF r) :=
  rfl

theorem absolutelyContinuous_expLaw (r : ℝ) :
    Measure.AbsolutelyContinuous (expLaw r) volume :=
  withDensity_absolutelyContinuous volume (exponentialPDF r)

private lemma measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

private lemma exponentialPDF_lt_top (r x : ℝ) : exponentialPDF r x < ⊤ :=
  ENNReal.ofReal_lt_top

theorem integrable_expLaw_iff {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ} :
    Integrable h (expLaw r) ↔
      Integrable (fun x ↦ h x * exponentialPDFReal r x) volume := by
  rw [expLaw_eq_withDensity,
    integrable_withDensity_iff (measurable_exponentialPDF r)
      (ae_of_all _ (exponentialPDF_lt_top r))]
  refine integrable_congr (ae_of_all _ fun x ↦ ?_)
  dsimp only [exponentialPDF, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr x), mul_comm]

theorem integrable_stdExpLaw_iff {h : ℝ → ℝ} :
    Integrable h stdExpLaw ↔
      IntegrableOn (fun x ↦ h x * Real.exp (-x)) (Ioi 0) volume := by
  rw [stdExpLaw, ← expLaw, integrable_expLaw_iff zero_lt_one]
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  have hsupp : (fun x ↦ h x * exponentialPDFReal 1 x) =ᵐ[volume]
      (Ioi (0 : ℝ)).indicator (fun x ↦ h x * Real.exp (-x)) := by
    filter_upwards [h0] with x hx
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hnot : ¬ 0 ≤ x := not_le.mpr hlt
      have hnot' : x ∉ Ioi (0 : ℝ) := not_lt.mpr hlt.le
      simp [exponentialPDFReal, gammaPDFReal, hnot, hnot']
    · exact False.elim (hx rfl)
    · have hle : 0 ≤ x := hgt.le
      have hmem : x ∈ Ioi (0 : ℝ) := hgt
      simp [exponentialPDFReal, gammaPDFReal, hle, hmem]
  rw [integrable_congr hsupp, integrable_indicator_iff measurableSet_Ioi]

theorem integral_expLaw_eq_setIntegral_Ioi {r : ℝ} (hr : 0 < r) (h : ℝ → ℝ) :
    ∫ x, h x ∂expLaw r = ∫ x in Ioi 0, h x * (r * Real.exp (-(r * x))) := by
  rw [expLaw_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (measurable_exponentialPDF r)
      (ae_of_all _ (exponentialPDF_lt_top r))]
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  have hsupp : (fun x ↦ (exponentialPDF r x).toReal • h x) =ᵐ[volume]
      (Ioi (0 : ℝ)).indicator (fun x ↦ h x * (r * Real.exp (-(r * x)))) := by
    filter_upwards [h0] with x hx
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hnot : ¬ 0 ≤ x := not_le.mpr hlt
      have hnot' : x ∉ Ioi (0 : ℝ) := not_lt.mpr hlt.le
      simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, hnot, hnot']
    · exact False.elim (hx rfl)
    · have hle : 0 ≤ x := hgt.le
      have hmem : x ∈ Ioi (0 : ℝ) := hgt
      simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, hle, hmem,
        ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_nonneg _)), mul_comm]
  rw [integral_congr_ae hsupp, integral_indicator measurableSet_Ioi]

theorem integral_stdExpLaw_eq_setIntegral_Ioi (h : ℝ → ℝ) :
    ∫ x, h x ∂stdExpLaw = ∫ x in Ioi 0, h x * Real.exp (-x) := by
  simpa using integral_expLaw_eq_setIntegral_Ioi zero_lt_one h

theorem stdExpExpect_eq_setIntegral_Ioi (h : ℝ → ℝ) :
    stdExpExpect h = ∫ x in Ioi 0, h x * Real.exp (-x) :=
  integral_stdExpLaw_eq_setIntegral_Ioi h

theorem expLaw_Iic_zero (r : ℝ) : expLaw r (Iic 0) = 0 := by
  rw [expLaw_eq_withDensity, withDensity_apply _ measurableSet_Iic, ← Iio_union_right,
    lintegral_union (measurableSet_singleton 0) (disjoint_singleton_right.mpr (by simp)),
    lintegral_exponentialPDF_of_nonpos le_rfl, zero_add]
  simp

theorem ae_pos_expLaw (r : ℝ) : ∀ᵐ x ∂expLaw r, 0 < x := by
  rw [ae_iff]
  convert expLaw_Iic_zero r using 2
  ext x
  simp

theorem ae_nonneg_expLaw (r : ℝ) : 0 ≤ᵐ[expLaw r] (id : ℝ → ℝ) :=
  (ae_pos_expLaw r).mono fun _ hx ↦ hx.le

theorem expLaw_real_Iic {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (expLaw r).real (Iic x) = if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0 := by
  have : IsProbabilityMeasure (expLaw r) := isProbabilityMeasure_expMeasure hr
  rw [← cdf_eq_real, cdf_expMeasure_eq hr]

theorem expLaw_real_Ioi {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    (expLaw r).real (Ioi x) = Real.exp (-(r * x)) := by
  have : IsProbabilityMeasure (expLaw r) := isProbabilityMeasure_expMeasure hr
  have hunion := measureReal_union (μ := expLaw r) (s₁ := Iic x) (s₂ := Ioi x)
    (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
  rw [Iic_union_Ioi, probReal_univ, expLaw_real_Iic hr, ite_eq_left hx] at hunion
  linarith

theorem expLaw_real_Ioc {r : ℝ} (hr : 0 < r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (expLaw r).real (Ioc a b) = Real.exp (-(r * a)) - Real.exp (-(r * b)) := by
  have : IsProbabilityMeasure (expLaw r) := isProbabilityMeasure_expMeasure hr
  have hunion := measureReal_union (μ := expLaw r) (s₁ := Iic a) (s₂ := Ioc a b)
    (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hab, expLaw_real_Iic hr, expLaw_real_Iic hr, ite_eq_left ha,
    ite_eq_left (ha.trans hab)] at hunion
  linarith

theorem integrableOn_exp_neg_Ioi (a : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi a) volume := by
  simpa using exp_neg_integrableOn_Ioi a zero_lt_one

theorem integral_exp_neg_Ioi (a : ℝ) :
    ∫ t in Ioi a, Real.exp (-t) = Real.exp (-a) := by
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun t : ℝ ↦ -Real.exp (-t)) (Real.exp (-x)) x := by
    intro x _
    simpa using hasDerivAt_neg_exp_mul_exp (r := 1) (x := x)
  have htend : Tendsto (fun t : ℝ ↦ -Real.exp (-t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_exp_neg_Ioi a) htend
  linarith

theorem integrable_id_stdExpLaw : Integrable (id : ℝ → ℝ) stdExpLaw := by
  rw [integrable_stdExpLaw_iff]
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  have _ : 0 ≤ x := le_of_lt hx
  simp only [id_eq, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

theorem integral_id_stdExpLaw : ∫ x, x ∂stdExpLaw = 1 := by
  rw [integral_stdExpLaw_eq_setIntegral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) (by norm_num) zero_lt_one
  have hcongr : ∫ x in Ioi (0 : ℝ), x * Real.exp (-x) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * Real.exp (-(1 * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    norm_num
  have hgamma2 : Real.Gamma 2 = 1 := by
    have : (2 : ℝ) = (1 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hcongr, h, hgamma2]
  norm_num

theorem memLp_id_two_stdExpLaw : MemLp (id : ℝ → ℝ) 2 stdExpLaw := by
  rw [memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable, integrable_stdExpLaw_iff]
  have h := Real.GammaIntegral_convergent (s := 3) (by norm_num)
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  have _ : 0 ≤ x := le_of_lt hx
  simp only [id_eq, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
  ring

theorem integral_sq_stdExpLaw : ∫ x, x ^ 2 ∂stdExpLaw = 2 := by
  rw [integral_stdExpLaw_eq_setIntegral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1) (by norm_num) zero_lt_one
  have hcongr : ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x) =
      ∫ x in Ioi (0 : ℝ), x ^ ((3 : ℝ) - 1) * Real.exp (-(1 * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    norm_num [Real.rpow_two]
  have hgamma3 : Real.Gamma 3 = 2 := by
    have : (3 : ℝ) = (2 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hcongr, h, hgamma3]
  norm_num

/-! ### Section 2: Shifted Geometric Distribution (`shiftedGeomLaw`) & Ceiling Witness -/

instance isProbabilityMeasure_shiftedGeomLaw (p : ℝ) :
    IsProbabilityMeasure (shiftedGeomLaw p) := by
  unfold shiftedGeomLaw
  infer_instance

theorem shiftedGeomLaw_zero (p : ℝ) : shiftedGeomLaw p {0} = 0 := by
  rw [shiftedGeomLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have hempty : ((· + 1) ⁻¹' ({0} : Set ℕ)) = ∅ := by
    ext n
    simp
  simp [hempty]

theorem ae_one_le_shiftedGeomLaw (p : ℝ) : ∀ᵐ n ∂shiftedGeomLaw p, 1 ≤ n := by
  rw [ae_iff]
  have hset : {n : ℕ | ¬ 1 ≤ n} = {0} := by
    ext n
    simp only [mem_ofPred_eq, mem_singleton_iff]
    omega
  rw [hset, shiftedGeomLaw_zero]

private lemma coe_projIcc_eq {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    (Set.projIcc 0 1 zero_le_one p : ℝ) = p :=
  congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hp₀.le, hp₁⟩)

private lemma projIcc_ne_zero {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    Set.projIcc 0 1 zero_le_one p ≠ 0 := by
  intro h0
  have : (Set.projIcc 0 1 zero_le_one p : ℝ) = 0 := congrArg Subtype.val h0
  linarith [coe_projIcc_eq hp₀ hp₁]

theorem shiftedGeomLaw_singleton_of_pos {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    shiftedGeomLaw p {k} = ENNReal.ofReal ((1 - p) ^ (k - 1) * p) := by
  rw [shiftedGeomLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton k)]
  have hpre : ((· + 1) ⁻¹' ({k} : Set ℕ)) = {k - 1} := by
    ext n
    simp only [mem_preimage, mem_singleton_iff]
    omega
  rw [hpre, geometricMeasure_singleton (projIcc_ne_zero hp₀ hp₁), coe_projIcc_eq hp₀ hp₁]

theorem shiftedGeomLaw_real_singleton_of_pos {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    (shiftedGeomLaw p).real {k} = (1 - p) ^ (k - 1) * p := by
  rw [measureReal_def, shiftedGeomLaw_singleton_of_pos hp₀ hp₁ hk,
    ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (sub_nonneg.mpr hp₁) _) hp₀.le)]

theorem shiftedGeomLaw_real_Ici {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) {m : ℕ} (_hm : 1 ≤ m) :
    (shiftedGeomLaw p).real (Ici m) = (1 - p) ^ (m - 1) := by
  have hproj := coe_projIcc_eq hp₀ hp₁
  have hp_ne := projIcc_ne_zero hp₀ hp₁
  rw [shiftedGeomLaw, map_measureReal_apply (by fun_prop) MeasurableSet.of_discrete]
  have hpre : ((· + 1) ⁻¹' Ici m) = Ici (m - 1) := by
    ext n
    simp only [mem_preimage, mem_Ici]
    omega
  rw [hpre]
  let ind : ℕ → ℝ := (Ici (m - 1)).indicator fun _ ↦ (1 : ℝ)
  have hint : ∫ n, ind n ∂geometricMeasure (Set.projIcc 0 1 zero_le_one p) =
      (geometricMeasure (Set.projIcc 0 1 zero_le_one p)).real (Ici (m - 1)) :=
    integral_indicator_one MeasurableSet.of_discrete
  rw [← hint, integral_geometricMeasure hp_ne, hproj]
  have hshift : (∑' n : ℕ, ((1 - p) ^ n * p) • ind n) =
      ∑' k : ℕ, (1 - p) ^ (k + (m - 1)) * p := by
    have hsum : Summable (fun n : ℕ ↦ ((1 - p) ^ n * p) • ind n) := by
      refine (hasSum_one_geometricMeasure hp_ne).summable.of_nonneg_of_le
        (fun n ↦ by
          dsimp [ind, indicator]
          split_ifs <;> positivity [sub_nonneg.mpr hp₁])
        (fun n ↦ ?_)
      rw [hproj]
      dsimp [ind, indicator]
      split_ifs <;> nlinarith [pow_nonneg (sub_nonneg.mpr hp₁) n]
    rw [← hsum.sum_add_tsum_nat_add (m - 1)]
    have hfin : ∑ i ∈ Finset.range (m - 1), ((1 - p) ^ i * p) • ind i = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      simp [ind, not_le.mpr hi]
    rw [hfin, zero_add]
    refine tsum_congr fun k ↦ ?_
    simp [ind]
  rw [hshift]
  have hpow : (fun k : ℕ ↦ (1 - p) ^ (k + (m - 1)) * p) =
      fun k : ℕ ↦ (1 - p) ^ (m - 1) * ((1 - p) ^ k * p) := by
    ext k; rw [pow_add]; ring
  rw [hpow, tsum_mul_left]
  have h1 := (hasSum_one_geometricMeasure hp_ne).tsum_eq
  rw [hproj] at h1
  rw [h1, mul_one]

theorem integrable_cast_shiftedGeomLaw {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    Integrable (fun n : ℕ ↦ (n : ℝ)) (shiftedGeomLaw p) := by
  rw [shiftedGeomLaw, integrable_map_measure (by fun_prop) (by fun_prop),
    integrable_geometricMeasure_iff (projIcc_ne_zero hp₀ hp₁), coe_projIcc_eq hp₀ hp₁]
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp₁)]
    linarith
  have hchoose := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr).summable.mul_right p
  refine hchoose.congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.choose_one_right, Nat.cast_add, Nat.cast_one,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  ring

theorem integral_cast_shiftedGeomLaw {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    ∫ n, (n : ℝ) ∂shiftedGeomLaw p = 1 / p := by
  rw [shiftedGeomLaw, integral_map (by fun_prop) (by fun_prop),
    integral_geometricMeasure (projIcc_ne_zero hp₀ hp₁), coe_projIcc_eq hp₀ hp₁]
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp₁)]
    linarith
  have hchoose := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr).mul_right p
  have heq : (fun n : ℕ ↦ ((1 - p) ^ n * p) • ((n + 1 : ℕ) : ℝ)) =
      fun n : ℕ ↦ ↑((n + 1).choose 1) * (1 - p) ^ n * p := by
    ext n
    simp only [smul_eq_mul, Nat.choose_one_right]
    ring
  rw [heq, hchoose.tsum_eq]
  have hp_ne' : p ≠ 0 := hp₀.ne'
  field_simp [hp_ne']
  ring

theorem memLp_cast_two_shiftedGeomLaw {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    MemLp (fun n : ℕ ↦ (n : ℝ)) 2 (shiftedGeomLaw p) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop), shiftedGeomLaw,
    integrable_map_measure (by fun_prop) (by fun_prop),
    integrable_geometricMeasure_iff (projIcc_ne_zero hp₀ hp₁), coe_projIcc_eq hp₀ hp₁]
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp₁)]
    linarith
  have h0 := summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr
  have h1 := summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 := summable_norm_pow_mul_geometric_of_norm_lt_one 2 hr
  have hdom : Summable fun n : ℕ ↦
      p * (‖(n : ℝ) ^ 2 * (1 - p) ^ n‖ + 2 * ‖(n : ℝ) ^ 1 * (1 - p) ^ n‖ +
        ‖(n : ℝ) ^ 0 * (1 - p) ^ n‖) :=
    ((h2.add (h1.mul_left 2)).add h0).mul_left p
  refine hdom.of_nonneg_of_le (fun _ ↦ by positivity [sub_nonneg.mpr hp₁]) (fun n ↦ ?_)
  have hr_nn : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr_nn,
    Nat.abs_cast, pow_zero, pow_one, one_mul]
  push_cast
  linarith

private lemma measurable_natCeil : Measurable (Nat.ceil : ℝ → ℕ) := by
  refine measurable_to_countable' fun k ↦ ?_
  rcases k with _ | m
  · have : (Nat.ceil ⁻¹' ({0} : Set ℕ) : Set ℝ) = Iic 0 := by
      ext x; simp
    rw [this]; exact measurableSet_Iic
  · have : (Nat.ceil ⁻¹' ({m + 1} : Set ℕ) : Set ℝ) = Ioc (m : ℝ) ((m : ℝ) + 1) := by
      ext x
      simp [Nat.ceil_eq_iff (Nat.succ_ne_zero m), Nat.cast_add, Nat.cast_one]
    rw [this]; exact measurableSet_Ioc

/-- Ceiling of $\mathrm{Exp}(\lambda)$ has law $\mathrm{Ge}(1 - e^{-\lambda})$
(Example 5.4 `\label{ex171}`, `SteinIntro.tex:2885-2886`; `ISSUE-TYPO-5.4`). -/
theorem expLaw_map_ceil_eq_shiftedGeomLaw {r : ℝ} (hr : 0 < r) :
    (expLaw r).map Nat.ceil = shiftedGeomLaw (1 - Real.exp (-r)) := by
  have : IsProbabilityMeasure (expLaw r) := isProbabilityMeasure_expMeasure hr
  have hp₀ : 0 < 1 - Real.exp (-r) := by
    have : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hp₁ : 1 - Real.exp (-r) ≤ 1 := by linarith [Real.exp_pos (-r)]
  ext s hs
  rw [← Measure.tsum_indicator_apply_singleton _ _ hs,
    ← Measure.tsum_indicator_apply_singleton (shiftedGeomLaw (1 - Real.exp (-r))) _ hs]
  congr with k
  by_cases hks : k ∈ s
  · simp only [indicator_of_mem hks]
    rcases k with _ | m
    · rw [Measure.map_apply measurable_natCeil (measurableSet_singleton 0), shiftedGeomLaw_zero]
      have : (Nat.ceil ⁻¹' ({0} : Set ℕ) : Set ℝ) = Iic 0 := by ext x; simp
      rw [this, expLaw_Iic_zero]
    · rw [Measure.map_apply measurable_natCeil (measurableSet_singleton (m + 1)),
        shiftedGeomLaw_singleton_of_pos hp₀ hp₁ (Nat.succ_le_succ (Nat.zero_le m))]
      have hpre : (Nat.ceil ⁻¹' ({m + 1} : Set ℕ) : Set ℝ) = Ioc (m : ℝ) ((m : ℝ) + 1) := by
        ext x
        simp [Nat.ceil_eq_iff (Nat.succ_ne_zero m), Nat.cast_add, Nat.cast_one]
      rw [hpre, ← ENNReal.ofReal_toReal (measure_ne_top (expLaw r) _),
        ← measureReal_def, expLaw_real_Ioc hr (Nat.cast_nonneg m) (by linarith)]
      congr 1
      have hexp1 : Real.exp (-(r * (m : ℝ))) = Real.exp (-r) ^ m := by
        rw [← Real.exp_nat_mul]
        ring_nf
      have hexp2 : Real.exp (-(r * ((m : ℝ) + 1))) = Real.exp (-r) ^ m * Real.exp (-r) := by
        rw [show -(r * ((m : ℝ) + 1)) = -(r * (m : ℝ)) + (-r) by ring, Real.exp_add, hexp1]
      rw [hexp1, hexp2, Nat.succ_sub_one]
      ring
  · simp [indicator_of_notMem hks]

/-- **Example 5.4, corrected ceiling prose claim** (`\label{ex171}`, `SteinIntro.tex:2885-2886`;
`ISSUE-TYPO-5.4`). -/
theorem ex5_4_ceil_corrected {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r : ℝ} {Z : Ω → ℝ}
    (hr : 0 < r) (hZ_meas : AEMeasurable Z P) (hZ_law : P.map Z = expLaw r) :
    P.map (fun ω ↦ Nat.ceil (Z ω)) = shiftedGeomLaw (1 - Real.exp (-r)) := by
  change P.map (Nat.ceil ∘ Z) = shiftedGeomLaw (1 - Real.exp (-r))
  rw [← AEMeasurable.map_map_of_aemeasurable measurable_natCeil.aemeasurable hZ_meas, hZ_law,
    expLaw_map_ceil_eq_shiftedGeomLaw hr]

/-! ### Section 3: Half-Line Integration by Parts & `IsEquilibrium` Non-Vacuity Witness -/

/-- Half-line Tonelli/Fubini integration by parts for $\mathrm{Exp}(1)$
(`SteinIntro.tex:2806-2810`): for locally absolutely continuous $f : \mathbb{R} \to \mathbb{R}$
with `Integrable (deriv f) stdExpLaw`, $f$ is integrable under `stdExpLaw` and
$\mathbb{E}[f(Z)] - f(0) = \mathbb{E}[f'(Z)]$. -/
theorem integrable_and_integral_sub_eq_deriv_stdExpLaw {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (deriv f) stdExpLaw) :
    Integrable f stdExpLaw ∧
      (∫ x, f x ∂stdExpLaw) - f 0 = ∫ x, deriv f x ∂stdExpLaw := by
  have hf'_on : IntegrableOn (fun t ↦ deriv f t * Real.exp (-t)) (Ioi 0) volume :=
    integrable_stdExpLaw_iff.mp hf'
  let S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1}
  let K : ℝ × ℝ → ℝ := S.indicator fun p ↦ deriv f p.2 * Real.exp (-p.1)
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hK_meas : Measurable K :=
    (Measurable.mul ((measurable_deriv f).comp measurable_snd)
      (measurable_fst.neg.exp)).indicator hS_meas
  have hK_int : Integrable K (volume.prod volume) := by
    rw [integrable_prod_iff' hK_meas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
    · by_cases ht : 0 < t
      · have h_ind : (fun x ↦ K (x, t)) =
            (Ioi t).indicator (fun x ↦ deriv f t * Real.exp (-x)) := by
          ext x; by_cases htx : t < x <;> simp [K, S, ht, htx]
        rw [h_ind, integrable_indicator_iff measurableSet_Ioi]
        exact (integrableOn_exp_neg_Ioi t).const_mul (deriv f t)
      · have h_zero : (fun x ↦ K (x, t)) = 0 := by ext x; simp [K, S, ht]
        rw [h_zero]; exact integrable_zero _ _ _
    · have h_norm_eq : (fun t ↦ ∫ x, ‖K (x, t)‖) =
          (Ioi (0 : ℝ)).indicator (fun t ↦ ‖deriv f t * Real.exp (-t)‖) := by
        ext t
        by_cases ht : 0 < t
        · have ht_mem : t ∈ Ioi (0 : ℝ) := ht
          have h_slice : (fun x ↦ ‖K (x, t)‖) =
              (Ioi t).indicator (fun x ↦ |deriv f t| * Real.exp (-x)) := by
            ext x
            by_cases htx : t < x
            · simp [K, S, ht, htx, abs_of_pos (Real.exp_pos _)]
            · simp [K, S, ht, htx]
          rw [h_slice, integral_indicator measurableSet_Ioi, integral_const_mul,
            integral_exp_neg_Ioi, indicator_of_mem ht_mem, Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos _)]
        · have ht_not : t ∉ Ioi (0 : ℝ) := ht
          have h_zero : (fun x ↦ ‖K (x, t)‖) = 0 := by ext x; simp [K, S, ht]
          rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem ht_not]
      rw [h_norm_eq, integrable_indicator_iff measurableSet_Ioi]
      exact hf'_on.norm
  have h_left : (fun x ↦ ∫ t, K (x, t)) =
      (Ioi (0 : ℝ)).indicator (fun x ↦ (f x - f 0) * Real.exp (-x)) := by
    ext x
    by_cases hx : 0 < x
    · have hx_mem : x ∈ Ioi (0 : ℝ) := hx
      have h_slice : (fun t ↦ K (x, t)) =
          (Ioo 0 x).indicator (fun t ↦ deriv f t * Real.exp (-x)) := by
        ext t; by_cases ht : 0 < t ∧ t < x <;> simp [K, S, ht]
      rw [h_slice, integral_indicator measurableSet_Ioo, integral_mul_const,
        setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hx.le,
        (hf 0 x).integral_deriv_eq_sub, indicator_of_mem hx_mem]
    · have hx_not : x ∉ Ioi (0 : ℝ) := hx
      have h_zero : (fun t ↦ K (x, t)) = 0 := by
        ext t
        have hnot : ¬ (0 < t ∧ t < x) := fun h ↦ hx (h.1.trans h.2)
        simp [K, S, hnot]
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem hx_not]
  have h_right : (fun t ↦ ∫ x, K (x, t)) =
      (Ioi (0 : ℝ)).indicator (fun t ↦ deriv f t * Real.exp (-t)) := by
    ext t
    by_cases ht : 0 < t
    · have ht_mem : t ∈ Ioi (0 : ℝ) := ht
      have h_slice : (fun x ↦ K (x, t)) =
          (Ioi t).indicator (fun x ↦ deriv f t * Real.exp (-x)) := by
        ext x; by_cases htx : t < x <;> simp [K, S, ht, htx]
      rw [h_slice, integral_indicator measurableSet_Ioi, integral_const_mul,
        integral_exp_neg_Ioi, indicator_of_mem ht_mem]
    · have ht_not : t ∉ Ioi (0 : ℝ) := ht
      have h_zero : (fun x ↦ K (x, t)) = 0 := by ext x; simp [K, S, ht]
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem ht_not]
  have hsub_on : IntegrableOn (fun x ↦ (f x - f 0) * Real.exp (-x)) (Ioi 0) volume := by
    rw [← integrable_indicator_iff measurableSet_Ioi, ← h_left]
    exact hK_int.integral_prod_left
  have hf_int : Integrable f stdExpLaw := by
    have hsub_int : Integrable (fun x ↦ f x - f 0) stdExpLaw :=
      integrable_stdExpLaw_iff.mpr hsub_on
    have heq : f = fun x ↦ (f x - f 0) + f 0 := by ext x; ring
    rw [heq]
    exact hsub_int.add (integrable_const (f 0))
  refine ⟨hf_int, ?_⟩
  have hfub : ∫ x, ∫ t, K (x, t) = ∫ t, ∫ x, K (x, t) := integral_integral_swap hK_int
  rw [h_left, integral_indicator measurableSet_Ioi, h_right,
    integral_indicator measurableSet_Ioi] at hfub
  rw [← integral_stdExpLaw_eq_setIntegral_Ioi (fun x ↦ f x - f 0),
    ← integral_stdExpLaw_eq_setIntegral_Ioi (deriv f)] at hfub
  have hint_sub : ∫ x, (f x - f 0) ∂stdExpLaw = (∫ x, f x ∂stdExpLaw) - f 0 := by
    rw [integral_sub hf_int (integrable_const (f 0)), integral_const]
    simp
  linarith

/-- **Non-vacuity witness for `IsEquilibrium`**: the equilibrium distribution of $\mathrm{Exp}(1)$
is $\mathrm{Exp}(1)$ itself (Definition 5.2, `SteinIntro.tex:2836-2843`). -/
theorem isEquilibrium_stdExpLaw : IsEquilibrium stdExpLaw id stdExpLaw id := by
  refine ⟨ae_nonneg_expLaw 1, integrable_id_stdExpLaw, measurable_id.aemeasurable, ?_⟩
  intro f ⟨K, hLip⟩
  have hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
    fun a b ↦ hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hf'_int : Integrable (deriv f) stdExpLaw := by
    refine Integrable.of_bound (measurable_deriv f).aestronglyMeasurable (K : ℝ)
      (ae_of_all _ fun x ↦ ?_)
    exact norm_deriv_le_of_lipschitz hLip
  have h := (integrable_and_integral_sub_eq_deriv_stdExpLaw hac hf'_int).2
  simpa [id_eq, integral_id_stdExpLaw] using h

end SteinMethod
