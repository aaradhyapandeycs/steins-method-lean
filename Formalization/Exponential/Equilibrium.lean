/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.MetricBounds
import Formalization.SizeBias.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-!
# Equilibrium Couplings, Density, Size-Bias Relation, and Scaling
(`Formalization.Exponential.Equilibrium`)

Formalizes Section 5.1 of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`, `SteinIntro.tex:2834-2894`):
* `sec5_1_equilibrium_ac` (`SteinIntro.tex:2844-2845`; `ISSUE-5.5`): uniqueness and Lebesgue
  density $x \mapsto \frac{1}{\mu}\mathbb{P}(W > x)\mathbf{1}_{(0, \infty)}(x)$ when $\mu > 0$.
* `integrable_and_integral_equilibrium_of_memLp_two`: $\mathbb{E}[W^e] = \mathbb{E}[W^2] / (2\mu)$
  for $W \in L^2$ with $\mu > 0$.
* `wassersteinDist_le_two_mul_lintegral_equilibrium` and `thm5_4` (**Theorem 5.4**,
  `\label{thm172}`, `SteinIntro.tex:2847-2853`): $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))
  \le 2\,\mathbb{E}|W^e - W|$.
* `prop5_5` (**Proposition 5.5**, `\label{prop171}`, `SteinIntro.tex:2863-2867`; literal per `D1`):
  $U W^s$ has the equilibrium distribution of $W$.
* `sec5_1_equilibrium_scale_restricted` (`SteinIntro.tex:2894`; `ISSUE-5.4`):
  $(cX)^e \stackrel{d}{=} c X^e$ for $c > 0$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Basic Invariance & Equilibrium Density (`Sec5_1_equilibrium_ac`) -/

/-- Law invariance of `IsEquilibrium` in both arguments (`SteinIntro.tex:2836-2843`). -/
theorem IsEquilibrium.congr_identDistrib
    {Ω₁ Ω₂ Ω₁' Ω₂' : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₁'] [MeasurableSpace Ω₂']
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P₁' : Measure Ω₁'} {P₂' : Measure Ω₂'}
    {W₁ : Ω₁ → ℝ} {W₂ : Ω₂ → ℝ} {We₁ : Ω₁' → ℝ} {We₂ : Ω₂' → ℝ}
    (hEq : IsEquilibrium P₁ W₁ P₁' We₁)
    (hW : IdentDistrib W₁ W₂ P₁ P₂) (hWe : IdentDistrib We₁ We₂ P₁' P₂') :
    IsEquilibrium P₂ W₂ P₂' We₂ := by
  rcases hEq with ⟨hW₁_nn, hW₁_int, _, hEq_id⟩
  have hW₂_nn : 0 ≤ᵐ[P₂] W₂ := by
    have hmap : ∀ᵐ x ∂(P₁.map W₁), 0 ≤ x :=
      (ae_map_iff hW.aemeasurable_fst measurableSet_Ici).mpr hW₁_nn
    rw [hW.map_eq] at hmap
    exact (ae_map_iff hW.aemeasurable_snd measurableSet_Ici).mp hmap
  refine ⟨hW₂_nn, hW.integrable_snd hW₁_int, hWe.aemeasurable_snd, fun f hf ↦ ?_⟩
  rcases hf with ⟨K, hLip⟩
  have hf_id : IdentDistrib (fun ω ↦ f (W₁ ω)) (fun ω ↦ f (W₂ ω)) P₁ P₂ :=
    hW.comp hLip.continuous.measurable
  have hdf_id : IdentDistrib (fun ω' ↦ deriv f (We₁ ω')) (fun ω' ↦ deriv f (We₂ ω')) P₁' P₂' :=
    hWe.comp (measurable_deriv f)
  rw [← hf_id.integral_eq, ← hW.integral_eq, ← hdf_id.integral_eq]
  exact hEq_id f ⟨K, hLip⟩

private lemma measurable_tailProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (W : Ω → ℝ) :
    Measurable fun x : ℝ ↦ P.real {ω | x < W ω} := by
  have hanti : Antitone fun x : ℝ ↦ P.real {ω | x < W ω} := fun x y hxy ↦
    measureReal_mono fun ω (h : y < W ω) ↦ lt_of_le_of_lt hxy h
  exact hanti.measurable

private lemma integrable_comp_of_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hW : Integrable W P) (hLip : LipschitzWith K f) :
    Integrable (fun ω ↦ f (W ω)) P := by
  have hdom : Integrable (fun ω ↦ |f 0| + (K : ℝ) * ‖W ω‖) P :=
    (integrable_const |f 0|).add (hW.norm.const_mul (K : ℝ))
  refine hdom.mono'
    (hLip.continuous.measurable.comp_aemeasurable hW.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hd := hLip.dist_le_mul (W ω) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, ← Real.norm_eq_abs (W ω)] at hd
  rw [Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (f (W ω)) (f 0)]

private lemma tail_tonelli_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ}
    (hW_nn : 0 ≤ᵐ[P] W) (hW_int : Integrable W P)
    {g : ℝ → ℝ} {C : ℝ} (hg_meas : Measurable g) (hg_bdd : ∀ x : ℝ, |g x| ≤ C) :
    IntegrableOn (fun x ↦ g x * P.real {ω | x < W ω}) (Ioi 0) volume ∧
      ∫ x in Ioi 0, g x * P.real {ω | x < W ω} =
        ∫ ω, (∫ x in Ioc 0 (W ω), g x) ∂P := by
  have hC0 : 0 ≤ C := (abs_nonneg (g 0)).trans (hg_bdd 0)
  set μW : Measure ℝ := P.map W
  have hW_aem : AEMeasurable W P := hW_int.aemeasurable
  have : IsProbabilityMeasure μW := (Measure.isProbabilityMeasure_map_iff hW_aem).mpr ‹_›
  have hid_int : Integrable (id : ℝ → ℝ) μW :=
    (integrable_map_measure aestronglyMeasurable_id hW_aem).mpr hW_int
  have hid_nn : ∀ᵐ y ∂μW, 0 ≤ y :=
    (ae_map_iff hW_aem measurableSet_Ici).mpr hW_nn
  let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
  let K : ℝ × ℝ → ℝ := S.indicator fun p ↦ g p.1
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hK_meas : Measurable K := (hg_meas.comp measurable_fst).indicator hS_meas
  have hK_int : Integrable K (volume.prod μW) := by
    rw [integrable_prod_iff' hK_meas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun y ↦ ?_, ?_⟩
    · by_cases hy : 0 < y
      · have h_slice : (fun x ↦ K (x, y)) = (Ioo 0 y).indicator g := by
          ext x; by_cases hx : 0 < x ∧ x < y <;> simp [K, S, hx]
        rw [h_slice, integrable_indicator_iff measurableSet_Ioo]
        refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
          hg_meas.aestronglyMeasurable C ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
        rw [Real.norm_eq_abs]; exact hg_bdd x
      · have h_zero : (fun x ↦ K (x, y)) = 0 := by
          ext x
          have hnot : ¬ (0 < x ∧ x < y) := fun h ↦ hy (h.1.trans h.2)
          simp [K, S, hnot]
        rw [h_zero]; exact integrable_zero _ _ _
    · refine (hid_int.norm.const_mul C).mono'
        (hK_meas.norm.stronglyMeasurable.integral_prod_left.aestronglyMeasurable)
        (ae_of_all _ fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)]
      by_cases hy : 0 < y
      · have h_slice : (fun x ↦ ‖K (x, y)‖) = (Ioo 0 y).indicator (fun x ↦ |g x|) := by
          ext x; by_cases hx : 0 < x ∧ x < y <;> simp [K, S, hx]
        rw [h_slice, integral_indicator measurableSet_Ioo]
        have hle : ∫ x in Ioo 0 y, |g x| ≤ ∫ _ in Ioo 0 y, C := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo fun x _ ↦ hg_bdd x
          · refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
              hg_meas.norm.aestronglyMeasurable C ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
            rw [Real.norm_eq_abs, abs_abs]; exact hg_bdd x
          · exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hy.le, sub_zero, smul_eq_mul,
          mul_comm] at hle
        exact hle.trans (mul_le_mul_of_nonneg_left (Real.le_norm_self y) hC0)
      · have h_zero : (fun x ↦ ‖K (x, y)‖) = 0 := by
          ext x
          have hnot : ¬ (0 < x ∧ x < y) := fun h ↦ hy (h.1.trans h.2)
          simp [K, S, hnot]
        rw [h_zero, Pi.zero_def, integral_zero]
        positivity
  have htail_eq : ∀ x : ℝ, μW.real (Ioi x) = P.real {ω | x < W ω} := fun x ↦ by
    rw [map_measureReal_apply_of_aemeasurable hW_aem measurableSet_Ioi]
    rfl
  have h_left : (fun x ↦ ∫ y, K (x, y) ∂μW) =
      (Ioi (0 : ℝ)).indicator (fun x ↦ g x * P.real {ω | x < W ω}) := by
    ext x
    by_cases hx : 0 < x
    · have hx_mem : x ∈ Ioi (0 : ℝ) := hx
      have h_slice : (fun y ↦ K (x, y)) = (Ioi x).indicator (fun _ ↦ g x) := by
        ext y; by_cases hxy : x < y <;> simp [K, S, hx, hxy]
      rw [h_slice, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm,
        htail_eq, indicator_of_mem hx_mem]
    · have hx_not : x ∉ Ioi (0 : ℝ) := hx
      have h_zero : (fun y ↦ K (x, y)) = 0 := by ext y; simp [K, S, hx]
      rw [h_zero, Pi.zero_def, integral_zero, indicator_of_notMem hx_not]
  have h_right : (fun y ↦ ∫ x, K (x, y)) = fun y ↦
      if 0 < y then ∫ x in Ioc 0 y, g x else 0 := by
    ext y
    split_ifs with hy
    · have h_slice : (fun x ↦ K (x, y)) = (Ioo 0 y).indicator g := by
        ext x; by_cases hx : 0 < x ∧ x < y <;> simp [K, S, hx]
      rw [h_slice, integral_indicator measurableSet_Ioo, setIntegral_congr_set Ioo_ae_eq_Ioc]
    · have h_zero : (fun x ↦ K (x, y)) = 0 := by
        ext x
        have hnot : ¬ (0 < x ∧ x < y) := fun h ↦ hy (h.1.trans h.2)
        simp [K, S, hnot]
      rw [h_zero, Pi.zero_def, integral_zero]
  have h_int_left : IntegrableOn (fun x ↦ g x * P.real {ω | x < W ω}) (Ioi 0) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mp (h_left ▸ hK_int.integral_prod_left)
  refine ⟨h_int_left, ?_⟩
  have hfub := (integral_prod K hK_int).symm.trans (integral_prod_symm K hK_int)
  rw [h_left, integral_indicator measurableSet_Ioi, h_right] at hfub
  have h_rhs_eq : (∫ y, (if 0 < y then ∫ x in Ioc 0 y, g x else 0) ∂μW) =
      ∫ y, (∫ x in Ioc 0 y, g x) ∂μW := by
    refine integral_congr_ae ?_
    filter_upwards [hid_nn] with y hy
    rcases hy.eq_or_lt with rfl | hpos
    · simp
    · simp [hpos]
  rw [h_rhs_eq] at hfub
  have hmeas_int : Measurable (fun y : ℝ ↦ ∫ x in Ioc 0 y, g x) := by
    have hg_loc : LocallyIntegrable g volume := by
      refine (locallyIntegrable_const C).mono_enorm hg_meas.aestronglyMeasurable
        (ae_of_all _ fun x ↦ ?_)
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
        Real.norm_eq_abs, abs_of_nonneg hC0]
      exact hg_bdd x
    have hcont : Continuous (fun y : ℝ ↦ ∫ x in (0 : ℝ)..y, g x) :=
      intervalIntegral.continuous_primitive (fun a b ↦
        intervalIntegrable_iff.mpr
          ((hg_loc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)) 0
    have heq : (fun y : ℝ ↦ ∫ x in Ioc 0 y, g x) =
        fun y ↦ if 0 ≤ y then ∫ x in (0 : ℝ)..y, g x else 0 := by
      ext y
      split_ifs with hy
      · rw [intervalIntegral.integral_of_le hy]
      · have hempty : Ioc 0 y = ∅ := Ioc_eq_empty (by linarith)
        simp [hempty]
    rw [heq]
    exact Measurable.ite measurableSet_Ici hcont.measurable measurable_const
  rw [hfub, integral_map hW_aem hmeas_int.aestronglyMeasurable]

/-- **Section 5.1 equilibrium uniqueness and Lebesgue absolute continuity**
(`SteinIntro.tex:2844-2845`; `ISSUE-5.5`): for $W \ge 0$ a.s. integrable with
$\mu = \mathbb{E}[W] > 0$, every equilibrium variable $W^e$ has the Lebesgue-AC law with density
$x \mapsto \frac{1}{\mu}\mathbb{P}(W > x)\mathbf{1}_{(0, \infty)}(x)$, and conversely this measure
is a probability measure absolutely continuous with respect to Lebesgue measure whose identity map
satisfies `IsEquilibrium`. -/
theorem sec5_1_equilibrium_ac {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ}
    (hW_nn : 0 ≤ᵐ[P] W) (hW_int : Integrable W P) (hμ_pos : 0 < ∫ ω, W ω ∂P) :
    let μ : ℝ := ∫ ω, W ω ∂P
    let ρ : ℝ → ℝ≥0∞ :=
      (Ioi (0 : ℝ)).indicator (fun x ↦ ENNReal.ofReal (P.real {ω | x < W ω} / μ))
    (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {We : Ω' → ℝ},
        IsEquilibrium P W P' We →
        P'.map We = volume.withDensity ρ ∧ Measure.AbsolutelyContinuous (P'.map We) volume) ∧
      (let ν : Measure ℝ := volume.withDensity ρ
       IsProbabilityMeasure ν ∧ Measure.AbsolutelyContinuous ν volume ∧
         IsEquilibrium P W ν id) := by
  dsimp only
  set μ : ℝ := ∫ ω, W ω ∂P
  set ρ : ℝ → ℝ≥0∞ :=
    (Ioi (0 : ℝ)).indicator (fun x ↦ ENNReal.ofReal (P.real {ω | x < W ω} / μ))
  set ν : Measure ℝ := volume.withDensity ρ
  have hρ_meas : Measurable ρ :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_tailProb P W).div_const μ)).indicator measurableSet_Ioi
  have hρ_lt_top : ∀ᵐ x ∂volume, ρ x < ⊤ := Eventually.of_forall fun x ↦ by
    dsimp only [ρ]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx]; exact ENNReal.ofReal_lt_top
    · rw [indicator_of_notMem hx]; exact ENNReal.zero_lt_top
  have hton1 := tail_tonelli_bounded P hW_nn hW_int (g := fun _ ↦ (1 : ℝ)) (C := 1)
    measurable_const (fun _ ↦ by norm_num)
  have htail_int : IntegrableOn (fun x ↦ P.real {ω | x < W ω}) (Ioi 0) volume := by
    simpa using hton1.1
  have htail_eq_μ : ∫ x in Ioi 0, P.real {ω | x < W ω} = μ := by
    have h1 := hton1.2
    simp only [one_mul, setIntegral_const, smul_eq_mul, mul_one] at h1
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hW_nn] with ω (hω : 0 ≤ W ω)
    rw [Real.volume_real_Ioc_of_le hω, sub_zero]
  have hν_prob : IsProbabilityMeasure ν := by
    rw [isProbabilityMeasure_iff]
    dsimp only [ν]
    rw [withDensity_apply ρ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_indicator measurableSet_Ioi]
    have hdiv_int : IntegrableOn (fun x ↦ P.real {ω | x < W ω} / μ) (Ioi 0) volume :=
      htail_int.div_const μ
    have hdiv_nn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun x ↦ P.real {ω | x < W ω} / μ :=
      Eventually.of_forall fun x ↦ div_nonneg measureReal_nonneg hμ_pos.le
    rw [← ofReal_integral_eq_lintegral_ofReal hdiv_int hdiv_nn, integral_div, htail_eq_μ,
      div_self hμ_pos.ne', ENNReal.ofReal_one]
  have hν_ac : Measure.AbsolutelyContinuous ν volume := withDensity_absolutelyContinuous volume ρ
  have hν_eq : IsEquilibrium P W ν id := by
    refine ⟨hW_nn, hW_int, aemeasurable_id, fun f ⟨K, hLip⟩ ↦ ?_⟩
    have hdf_bdd : ∀ x : ℝ, |deriv f x| ≤ K := fun x ↦ by
      simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := x) hLip
    have hton := tail_tonelli_bounded P hW_nn hW_int (measurable_deriv f) hdf_bdd
    have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
      fun a b ↦ hLip.lipschitzOnWith.absolutelyContinuousOnInterval
    have hfW_int : Integrable (fun ω ↦ f (W ω)) P := integrable_comp_of_lipschitz hW_int hLip
    have h_rhs : ∫ x, deriv f x ∂ν = μ⁻¹ * ∫ x in Ioi 0, deriv f x * P.real {ω | x < W ω} := by
      rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
      have hcongr : (fun x : ℝ ↦ (ρ x).toReal • deriv f x) =
          (Ioi (0 : ℝ)).indicator (fun x ↦ μ⁻¹ * (deriv f x * P.real {ω | x < W ω})) := by
        ext x
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hx, smul_eq_mul]
          dsimp only [ρ]
          rw [indicator_of_mem hx,
            ENNReal.toReal_ofReal (div_nonneg measureReal_nonneg hμ_pos.le)]
          ring
        · simp [ρ, hx]
      rw [hcongr, integral_indicator measurableSet_Ioi, integral_const_mul]
    have h_ftc : ∫ ω, (∫ x in Ioc 0 (W ω), deriv f x) ∂P = (∫ ω, f (W ω) ∂P) - f 0 := by
      have hae : (fun ω ↦ ∫ x in Ioc 0 (W ω), deriv f x) =ᵐ[P] fun ω ↦ f (W ω) - f 0 := by
        filter_upwards [hW_nn] with ω (hω : 0 ≤ W ω)
        rw [← intervalIntegral.integral_of_le hω, (hf_ac 0 (W ω)).integral_deriv_eq_sub]
      rw [integral_congr_ae hae, integral_sub hfW_int (integrable_const (f 0)), integral_const,
        probReal_univ, one_smul]
    simp only [id_eq]
    rw [h_rhs, hton.2, h_ftc, ← mul_assoc, mul_inv_cancel₀ hμ_pos.ne', one_mul]
  refine ⟨fun P' _ We hWe ↦ ?_, hν_prob, hν_ac, hν_eq⟩
  have : IsProbabilityMeasure (P'.map We) :=
    (Measure.isProbabilityMeasure_map_iff hWe.2.2.1).mpr ‹_›
  have hmap_eq : P'.map We = ν := by
    refine Measure.eq_of_cdf (P'.map We) ν ?_
    ext a
    have heq_n : ∀ n : ℕ, ∫ u, expRamp a n u ∂(P'.map We) = ∫ u, expRamp a n u ∂ν := by
      intro n
      let g := expRamp a n
      have hg_cont : Continuous g := continuous_expRamp a n
      let G : ℝ → ℝ := fun u ↦ ∫ t in (0 : ℝ)..u, g t
      have hG_deriv : ∀ u : ℝ, HasDerivAt G (g u) u := fun u ↦
        intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 u)
          hg_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hg_cont.continuousAt
      have hG_deriv_eq : deriv G = g := funext fun u ↦ (hG_deriv u).deriv
      have hG_lip : LipschitzWith 1 G := by
        refine LipschitzWith.mk_one fun u v ↦ ?_
        rw [Real.dist_eq, Real.dist_eq]
        have hdiff : G u - G v = ∫ t in v..u, g t := by
          dsimp only [G]
          rw [intervalIntegral.integral_interval_sub_left (hg_cont.intervalIntegrable 0 u)
            (hg_cont.intervalIntegrable 0 v)]
        rw [hdiff]
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := v) (b := u) (C := 1)
          (f := g) fun t _ ↦ by rw [Real.norm_eq_abs]; exact abs_expRamp_le_one a n t
        rwa [Real.norm_eq_abs, one_mul] at hb
      have h1 := hWe.2.2.2 G ⟨1, hG_lip⟩
      have h2 := hν_eq.2.2.2 G ⟨1, hG_lip⟩
      rw [hG_deriv_eq] at h1 h2
      have hmul : μ * ∫ ω', g (We ω') ∂P' = μ * ∫ x, g x ∂ν := h1.symm.trans h2
      have hint_eq := mul_left_cancel₀ hμ_pos.ne' hmul
      rwa [integral_map hWe.2.2.1 hg_cont.aestronglyMeasurable]
    have hlim1 := tendsto_integral_expRamp (P'.map We) a
    have hlim2 := tendsto_integral_expRamp ν a
    simp_rw [heq_n] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2
  exact ⟨hmap_eq, hmap_eq ▸ hν_ac⟩

/-! ### Section 2: First Moment of $W^e$ under $L^2$ and Theorem 5.4 (`Thm5_4`) -/

/-- When $W \ge 0$ a.s. belongs to $L^2(P)$ with $\mu = \mathbb{E}[W] > 0$, any equilibrium
variable $W^e$ is a.s. non-negative and integrable with $\mathbb{E}[W^e] = \mathbb{E}[W^2]/(2\mu)$
(`SteinIntro.tex:2847-2853, 2980`). -/
theorem integrable_and_integral_equilibrium_of_memLp_two
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {We : Ω' → ℝ}
    (hW_nn : 0 ≤ᵐ[P] W) (hW2 : MemLp W 2 P) (hμ_pos : 0 < ∫ ω, W ω ∂P)
    (hEq : IsEquilibrium P W P' We) :
    (0 ≤ᵐ[P'] We) ∧ Integrable We P' ∧
      ∫ ω', We ω' ∂P' = (∫ ω, W ω ^ 2 ∂P) / (2 * ∫ ω, W ω ∂P) := by
  have hW_int : Integrable W P := hW2.integrable one_le_two
  set μ : ℝ := ∫ ω, W ω ∂P
  set ρ : ℝ → ℝ≥0∞ :=
    (Ioi (0 : ℝ)).indicator (fun x ↦ ENNReal.ofReal (P.real {ω | x < W ω} / μ))
  have hmap : P'.map We = volume.withDensity ρ :=
    ((sec5_1_equilibrium_ac P hW_nn hW_int hμ_pos).1 P' hEq).1
  have hWe_nn : 0 ≤ᵐ[P'] We := by
    refine (ae_map_iff hEq.2.2.1 measurableSet_Ici).mp ?_
    rw [hmap, ae_iff]
    change (volume.withDensity ρ) {x : ℝ | ¬ (0 : ℝ) ≤ x} = 0
    have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = Iio (0 : ℝ) := by ext x; simp
    rw [hset, withDensity_apply ρ measurableSet_Iio]
    have hzero : ∫⁻ x in Iio (0 : ℝ), ρ x = ∫⁻ (_ : ℝ) in Iio (0 : ℝ), 0 :=
      setLIntegral_congr_fun measurableSet_Iio fun x (hx : x < 0) ↦
        indicator_of_notMem (not_lt.mpr hx.le) _
    rw [hzero, lintegral_zero]
  let gM : ℕ → ℝ → ℝ := fun M t ↦ min (max t 0) (M : ℝ)
  let GM : ℕ → ℝ → ℝ := fun M w ↦ ∫ t in (0 : ℝ)..w, gM M t
  have hgM_cont : ∀ M : ℕ, Continuous (gM M) := fun M ↦
    (continuous_id.max continuous_const).min continuous_const
  have hgM_nn : ∀ (M : ℕ) (t : ℝ), 0 ≤ gM M t := fun M t ↦
    le_min (le_max_right t 0) (Nat.cast_nonneg M)
  have hgM_le : ∀ (M : ℕ) (t : ℝ), gM M t ≤ (M : ℝ) := fun _ _ ↦ min_le_right _ _
  have hGM_deriv : ∀ (M : ℕ) (w : ℝ), HasDerivAt (GM M) (gM M w) w := fun M w ↦
    intervalIntegral.integral_hasDerivAt_right ((hgM_cont M).intervalIntegrable 0 w)
      (hgM_cont M).aestronglyMeasurable.stronglyMeasurableAtFilter (hgM_cont M).continuousAt
  have hGM_lip : ∀ M : ℕ, LipschitzWith (M : ℝ≥0) (GM M) := fun M ↦ by
    refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_natCast]
    have hdiff : GM M u - GM M v = ∫ t in v..u, gM M t :=
      intervalIntegral.integral_interval_sub_left ((hgM_cont M).intervalIntegrable 0 u)
        ((hgM_cont M).intervalIntegrable 0 v)
    rw [hdiff]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := v) (b := u) (C := (M : ℝ))
      (f := gM M) fun t _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgM_nn M t)]
        exact hgM_le M t
    rwa [Real.norm_eq_abs] at hb
  have hGM_id : ∀ M : ℕ, ∫ ω, GM M (W ω) ∂P = μ * ∫ ω', gM M (We ω') ∂P' := fun M ↦ by
    have h := hEq.2.2.2 (GM M) ⟨(M : ℝ≥0), hGM_lip M⟩
    have h0 : GM M 0 = 0 := intervalIntegral.integral_same
    have hder : deriv (GM M) = gM M := funext fun w ↦ (hGM_deriv M w).deriv
    simpa [h0, hder] using h
  have hid_sq : ∀ w : ℝ, ∫ t in (0 : ℝ)..w, t = w ^ 2 / 2 := fun w ↦ by
    have hd : ∀ t ∈ uIcc (0 : ℝ) w, HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := fun t _ ↦ by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (continuous_id.intervalIntegrable 0 w)]
    ring
  have hGM_eq_of_le : ∀ {M : ℕ} {w : ℝ}, 0 ≤ w → w ≤ (M : ℝ) → GM M w = w ^ 2 / 2 := by
    intro M w hw hwM
    dsimp only [GM]
    have hcongr : EqOn (gM M) id (uIcc (0 : ℝ) w) := fun t ht ↦ by
      rw [uIcc_of_le hw] at ht
      dsimp only [gM, id]
      rw [max_eq_left ht.1, min_eq_left (ht.2.trans hwM)]
    rw [intervalIntegral.integral_congr hcongr]
    simp [hid_sq]
  have hGM_bdd : ∀ (M : ℕ) {w : ℝ}, 0 ≤ w → 0 ≤ GM M w ∧ GM M w ≤ w ^ 2 / 2 := by
    intro M w hw
    refine ⟨intervalIntegral.integral_nonneg hw fun t _ ↦ hgM_nn M t, ?_⟩
    rw [← hid_sq]
    refine intervalIntegral.integral_mono_on hw ((hgM_cont M).intervalIntegrable 0 w)
      (continuous_id.intervalIntegrable 0 w) fun t ht ↦ ?_
    exact (min_le_left _ _).trans (max_eq_left ht.1).le
  have hW_sq_int : Integrable (fun ω ↦ W ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hW_int.aestronglyMeasurable).mp hW2
  have hGM_tendsto :
      Tendsto (fun M : ℕ ↦ ∫ ω, GM M (W ω) ∂P) atTop (𝓝 (∫ ω, W ω ^ 2 / 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω ↦ W ω ^ 2 / 2)
      (fun M ↦ ((hGM_lip M).continuous.measurable.comp_aemeasurable
        hW_int.aemeasurable).aestronglyMeasurable)
      (hW_sq_int.div_const 2) ?_ ?_
    · intro M
      filter_upwards [hW_nn] with ω (hω : 0 ≤ W ω)
      rw [Real.norm_eq_abs, abs_of_nonneg (hGM_bdd M hω).1]
      exact (hGM_bdd M hω).2
    · filter_upwards [hW_nn] with ω (hω : 0 ≤ W ω)
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (W ω)) fun M hM ↦ ?_
      exact hGM_eq_of_le hω ((Nat.le_ceil (W ω)).trans (Nat.cast_le.mpr hM))
  have hgM_int : ∀ M : ℕ, Integrable (fun ω' ↦ gM M (We ω')) P' := fun M ↦ by
    refine Integrable.of_bound
      ((hgM_cont M).measurable.comp_aemeasurable hEq.2.2.1).aestronglyMeasurable
      (M : ℝ) (Eventually.of_forall fun ω' ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgM_nn M (We ω'))]
    exact hgM_le M (We ω')
  have hWe_lint : ∫⁻ ω', ‖We ω'‖ₑ ∂P' < ⊤ := by
    have hae_enorm :
        (fun ω' ↦ ‖We ω'‖ₑ) =ᵐ[P'] fun ω' ↦ ⨆ M : ℕ, ENNReal.ofReal (gM M (We ω')) := by
      filter_upwards [hWe_nn] with ω' (hω' : 0 ≤ We ω')
      rw [Real.enorm_eq_ofReal hω']
      refine le_antisymm ?_ (iSup_le fun M ↦ ENNReal.ofReal_le_ofReal ?_)
      · let M₀ : ℕ := Nat.ceil (We ω')
        have h_eq : gM M₀ (We ω') = We ω' := by
          dsimp only [gM]
          rw [max_eq_left hω', min_eq_left (Nat.le_ceil (We ω'))]
        calc
          ENNReal.ofReal (We ω') = ENNReal.ofReal (gM M₀ (We ω')) := by rw [h_eq]
          _ ≤ ⨆ M : ℕ, ENNReal.ofReal (gM M (We ω')) :=
            le_iSup (fun M : ℕ ↦ ENNReal.ofReal (gM M (We ω'))) M₀
      · dsimp only [gM]
        rw [max_eq_left hω']
        exact min_le_left _ _
    rw [lintegral_congr_ae hae_enorm]
    have hmono : Monotone (fun (M : ℕ) ω' ↦ ENNReal.ofReal (gM M (We ω'))) := fun M₁ M₂ hle ω' ↦
      ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hle))
    have haemeas : ∀ M : ℕ, AEMeasurable (fun ω' ↦ ENNReal.ofReal (gM M (We ω'))) P' := fun M ↦
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hgM_cont M).measurable.comp_aemeasurable hEq.2.2.1)
    rw [lintegral_iSup' haemeas (Eventually.of_forall fun ω' M₁ M₂ hle ↦ hmono hle ω')]
    refine lt_of_le_of_lt (iSup_le fun M ↦ ?_)
      (ENNReal.ofReal_lt_top (r := (∫ ω, W ω ^ 2 / 2 ∂P) / μ))
    rw [← ofReal_integral_eq_lintegral_ofReal (hgM_int M)
      (Eventually.of_forall fun ω' ↦ hgM_nn M (We ω'))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hμ_pos, mul_comm, ← hGM_id M]
    refine integral_mono_ae ?_ (hW_sq_int.div_const 2) ?_
    · exact integrable_comp_of_lipschitz hW_int (hGM_lip M)
    · filter_upwards [hW_nn] with ω (hω : 0 ≤ W ω)
      exact (hGM_bdd M hω).2
  have hWe_int : Integrable We P' := ⟨hEq.2.2.1.aestronglyMeasurable, hWe_lint⟩
  have hgM_We_tendsto :
      Tendsto (fun M : ℕ ↦ ∫ ω', gM M (We ω') ∂P') atTop (𝓝 (∫ ω', We ω' ∂P')) := by
    refine tendsto_integral_of_dominated_convergence (fun ω' ↦ |We ω'|)
      (fun M ↦ ((hgM_cont M).measurable.comp_aemeasurable hEq.2.2.1).aestronglyMeasurable)
      hWe_int.norm ?_ ?_
    · intro M
      filter_upwards [hWe_nn] with ω' (hω' : 0 ≤ We ω')
      rw [Real.norm_eq_abs, abs_of_nonneg (hgM_nn M (We ω')), abs_of_nonneg hω']
      dsimp only [gM]
      rw [max_eq_left hω']
      exact min_le_left _ _
    · filter_upwards [hWe_nn] with ω' (hω' : 0 ≤ We ω')
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (We ω')) fun M hM ↦ ?_
      dsimp only [gM]
      rw [max_eq_left hω', min_eq_left ((Nat.le_ceil (We ω')).trans (Nat.cast_le.mpr hM))]
  have hlim_eq : ∫ ω, W ω ^ 2 / 2 ∂P = μ * ∫ ω', We ω' ∂P' := by
    have h2 := hgM_We_tendsto.const_mul μ
    simp_rw [← hGM_id] at h2
    exact tendsto_nhds_unique hGM_tendsto h2
  refine ⟨hWe_nn, hWe_int, ?_⟩
  rw [integral_div 2 (fun ω ↦ W ω ^ 2)] at hlim_eq
  refine (eq_div_iff (mul_ne_zero two_ne_zero hμ_pos.ne')).mpr ?_
  linarith [hlim_eq]

/-- General `ℝ≥0∞` exponential equilibrium coupling bound (`SteinIntro.tex:2847-2860`): requires
only $W \in L^1(P)$ with $\mathbb{E}[W] = 1$ (without needing $W \in L^2$ or $W^e \in L^1$),
avoiding any Bochner junk zero when $\mathbb{E}|W^e - W| = \infty$. -/
theorem wassersteinDist_le_two_mul_lintegral_equilibrium
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W We : Ω → ℝ} {Z : Ω' → ℝ}
    (hW_nn : 0 ≤ᵐ[P] W) (hW_int : Integrable W P) (hW_mean : ∫ ω, W ω ∂P = 1)
    (hEq : IsEquilibrium P W P We)
    (hZ_meas : AEMeasurable Z P') (hZ_law : P'.map Z = stdExpLaw) :
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal |We ω - W ω| ∂P := by
  refine (thm5_3_1 P P' hW_nn hW_int hZ_meas hZ_law).trans ?_
  refine iSup₂_le fun f hf ↦ ?_
  rcases hf with ⟨hf_diff, hf'_diff, hf'_bdd, hf''_bdd, hf0⟩
  have hf_lip : LipschitzWith 1 f := by
    refine lipschitzWith_of_nnnorm_deriv_le hf_diff fun x ↦ ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
    exact hf'_bdd x
  have hdf_lip : LipschitzWith 2 (deriv f) := by
    refine lipschitzWith_of_nnnorm_deriv_le hf'_diff fun x ↦ ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
    exact hf''_bdd x
  have hEq_f := hEq.2.2.2 f ⟨1, hf_lip⟩
  rw [hf0, sub_zero, hW_mean, one_mul] at hEq_f
  have hdfW_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    Integrable.of_bound
      ((measurable_deriv f).comp_aemeasurable hW_int.aemeasurable).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf'_bdd (W ω))
  have hdfWe_int : Integrable (fun ω ↦ deriv f (We ω)) P :=
    Integrable.of_bound
      ((measurable_deriv f).comp_aemeasurable hEq.2.2.1).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf'_bdd (We ω))
  have hfW_int : Integrable (fun ω ↦ f (W ω)) P := integrable_comp_of_lipschitz hW_int hf_lip
  have hsub_eq : ∫ ω, (deriv f (W ω) - f (W ω)) ∂P =
      ∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P := by
    rw [integral_sub hdfW_int hfW_int, hEq_f, ← integral_sub hdfW_int hdfWe_int]
  rw [hsub_eq]
  have hnorm_int : Integrable (fun ω ↦ |deriv f (W ω) - deriv f (We ω)|) P :=
    (hdfW_int.sub hdfWe_int).norm
  have hle_abs : |∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P| ≤
      ∫ ω, |deriv f (W ω) - deriv f (We ω)| ∂P := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun ω ↦ deriv f (W ω) - deriv f (We ω))
  have hae_diff_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal |We ω - W ω|) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable (hEq.2.2.1.sub hW_int.aemeasurable))
  calc
    ENNReal.ofReal |∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P|
        ≤ ENNReal.ofReal (∫ ω, |deriv f (W ω) - deriv f (We ω)| ∂P) :=
          ENNReal.ofReal_le_ofReal hle_abs
    _ = ∫⁻ ω, ENNReal.ofReal |deriv f (W ω) - deriv f (We ω)| ∂P :=
          ofReal_integral_eq_lintegral_ofReal hnorm_int
            (Eventually.of_forall fun _ ↦ abs_nonneg _)
    _ ≤ ∫⁻ ω, ENNReal.ofReal 2 * ENNReal.ofReal |We ω - W ω| ∂P := by
          refine lintegral_mono fun ω ↦ ?_
          rw [← ENNReal.ofReal_mul zero_le_two]
          refine ENNReal.ofReal_le_ofReal ?_
          have hd := hdf_lip.dist_le_mul (W ω) (We ω)
          rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat, abs_sub_comm (W ω) (We ω)] at hd
    _ = ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal |We ω - W ω| ∂P :=
          lintegral_const_mul'' (ENNReal.ofReal 2) hae_diff_meas

/-- **Theorem 5.4** (`\label{thm172}`, `SteinIntro.tex:2847-2853`): if $W \ge 0$ a.s. satisfies
$\mathbb{E}[W] = 1$ and $\mathbb{E}[W^2] < \infty$, $W^e$ has the equilibrium distribution with
respect to $W$ on the same probability space, and $Z \sim \mathrm{Exp}(1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le 2\,\mathbb{E}|W^e - W|$.
Note: the Bochner integral on the right-hand side is genuine (not junk zero) because $W \in L^2(P)$
and $\mathbb{E}[W] = 1$ imply $W^e \in L^1(P)$ with $\mathbb{E}[W^e] = \mathbb{E}[W^2]/2 < \infty$
(`integrable_and_integral_equilibrium_of_memLp_two`). For the $L^1$-only `ℝ≥0∞` version, see
`wassersteinDist_le_two_mul_lintegral_equilibrium`. -/
theorem thm5_4 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W We : Ω → ℝ} {Z : Ω' → ℝ}
    (hW_nn : 0 ≤ᵐ[P] W) (hW2 : MemLp W 2 P) (hW_mean : ∫ ω, W ω ∂P = 1)
    (hEq : IsEquilibrium P W P We)
    (hZ_meas : AEMeasurable Z P') (hZ_law : P'.map Z = stdExpLaw) :
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (2 * ∫ ω, |We ω - W ω| ∂P) := by
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hμ_pos : 0 < ∫ ω, W ω ∂P := by rw [hW_mean]; exact zero_lt_one
  have hWe_int : Integrable We P :=
    (integrable_and_integral_equilibrium_of_memLp_two P P hW_nn hW2 hμ_pos hEq).2.1
  have hdiff_int : Integrable (fun ω ↦ |We ω - W ω|) P := (hWe_int.sub hW_int).norm
  refine (wassersteinDist_le_two_mul_lintegral_equilibrium P P' hW_nn hW_int hW_mean hEq
    hZ_meas hZ_law).trans_eq ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hdiff_int (Eventually.of_forall fun _ ↦ abs_nonneg _),
    ← ENNReal.ofReal_mul zero_le_two]

/-! ### Section 3: Size-Bias Relation (`Prop5_5`), Scaling, and Geometric Example (`Ex5_4`) -/

private lemma map_eq_restrict_Ioo_of_isUniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → ℝ} (hU : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P) :
    P.map U = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [hU.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
    inv_one, one_smul]

/-- **Proposition 5.5** (`\label{prop171}`, `SteinIntro.tex:2863-2867`; literal per `D1`): if
$W \ge 0$ a.s. is integrable, $W^s$ has the size-bias distribution of $W$, and $U$ is uniform on
$(0, 1)$ independent of $W^s$, then $U W^s$ has the equilibrium distribution of $W$. -/
theorem prop5_5 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Ws U : Ω' → ℝ}
    (hW_nn : 0 ≤ᵐ[P] W) (hW_int : Integrable W P)
    (hSB : IsSizeBias P W P' Ws)
    (hU : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P')
    (hIndep : IndepFun U Ws P') :
    IsEquilibrium P W P' (fun ω' ↦ U ω' * Ws ω') := by
  refine ⟨hW_nn, hW_int, hU.aemeasurable.mul hSB.2.2.1, fun f ⟨K, hLip⟩ ↦ ?_⟩
  set μ : ℝ := ∫ ω, W ω ∂P
  have hμ_nn : 0 ≤ μ := integral_nonneg_of_ae hW_nn
  rcases hμ_nn.eq_or_lt with hμ0 | hμ_pos
  · have hW0 : W =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hW_nn hW_int).mp hμ0.symm
    have hfW : (fun ω ↦ f (W ω)) =ᵐ[P] fun _ ↦ f 0 := hW0.mono fun ω hω ↦ by simp [hω]
    rw [integral_congr_ae hfW, integral_const, probReal_univ, one_smul, sub_self, ← hμ0, zero_mul]
  · have hU_map := map_eq_restrict_Ioo_of_isUniform hU
    have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
      rw [← hU_map]
      exact (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr ‹_›
    set νs : Measure ℝ := P'.map Ws
    have : IsProbabilityMeasure νs :=
      (Measure.isProbabilityMeasure_map_iff hSB.2.2.1).mpr ‹_›
    have hprod_map : P'.map (fun ω' ↦ (U ω', Ws ω')) =
        (volume.restrict (Ioo (0 : ℝ) 1)).prod νs := by
      rw [hIndep.map_prod_eq_prod_map_map hU.aemeasurable hSB.2.2.1, hU_map]
    let φ : ℝ × ℝ → ℝ := fun p ↦ deriv f (p.1 * p.2)
    have hφ_meas : Measurable φ := (measurable_deriv f).comp (measurable_fst.mul measurable_snd)
    have hdf_bdd : ∀ y : ℝ, |deriv f y| ≤ K := fun y ↦ by
      simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
    have hφ_int : Integrable φ ((volume.restrict (Ioo (0 : ℝ) 1)).prod νs) :=
      Integrable.of_bound hφ_meas.aestronglyMeasurable K
        (Eventually.of_forall fun p ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd (p.1 * p.2))
    have hprod_aem : AEMeasurable (fun ω' ↦ (U ω', Ws ω')) P' :=
      hU.aemeasurable.prodMk hSB.2.2.1
    have h_int_eq : ∫ ω', deriv f (U ω' * Ws ω') ∂P' =
        ∫ x, (∫ u in Ioo (0 : ℝ) 1, deriv f (u * x)) ∂νs := by
      have h1 : (fun ω' ↦ deriv f (U ω' * Ws ω')) = fun ω' ↦ φ (U ω', Ws ω') := rfl
      rw [h1, ← integral_map hprod_aem hφ_meas.aestronglyMeasurable, hprod_map,
        integral_prod_symm φ hφ_int]
    have hνs_eq : νs = (P.map W).withDensity (fun x ↦ ENNReal.ofReal (x / μ)) :=
      (sizeBias_law_characterization P hW_nn hW_int hμ_pos).1 P' hSB
    let d : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (x / μ)
    have hd_meas : Measurable d := ENNReal.measurable_ofReal.comp (measurable_id.div_const μ)
    have h_wd : ∫ x, (∫ u in Ioo (0 : ℝ) 1, deriv f (u * x)) ∂νs =
        ∫ x, (d x).toReal • (∫ u in Ioo (0 : ℝ) 1, deriv f (u * x)) ∂(P.map W) := by
      rw [hνs_eq]
      exact integral_withDensity_eq_integral_toReal_smul hd_meas
        (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _
    have hid_nn : ∀ᵐ x ∂(P.map W), 0 ≤ x :=
      (ae_map_iff hW_int.aemeasurable measurableSet_Ici).mpr hW_nn
    have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
      fun a b ↦ hLip.lipschitzOnWith.absolutelyContinuousOnInterval
    have hae_eval :
        (fun x : ℝ ↦ (d x).toReal • (∫ u in Ioo (0 : ℝ) 1, deriv f (u * x))) =ᵐ[P.map W]
          fun x ↦ μ⁻¹ * (f x - f 0) := by
      filter_upwards [hid_nn] with x hx
      dsimp only [d]
      rw [ENNReal.toReal_ofReal (div_nonneg hx hμ_pos.le), smul_eq_mul]
      rcases hx.eq_or_lt with rfl | hx_pos
      · simp
      · rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_comp_mul_right (deriv f) hx_pos.ne', zero_mul, one_mul,
          smul_eq_mul, (hf_ac 0 x).integral_deriv_eq_sub, div_eq_mul_inv]
        field_simp [hx_pos.ne', hμ_pos.ne']
    have hfW_int : Integrable (fun ω ↦ f (W ω)) P := integrable_comp_of_lipschitz hW_int hLip
    rw [h_int_eq, h_wd, integral_congr_ae hae_eval, integral_const_mul,
      integral_map hW_int.aemeasurable
        ((hLip.continuous.fun_sub continuous_const).measurable.aestronglyMeasurable),
      integral_sub hfW_int (integrable_const (f 0)), integral_const, probReal_univ, one_smul,
      ← mul_assoc, mul_inv_cancel₀ hμ_pos.ne', one_mul]

private lemma deriv_comp_mul_left_eq' (f : ℝ → ℝ) {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    deriv (fun t ↦ f (c * t)) x = c * deriv f (c * x) := by
  by_cases hdiff : DifferentiableAt ℝ f (c * x)
  · have hd : HasDerivAt (fun t ↦ f (c * t)) (deriv f (c * x) * c) x :=
      hdiff.hasDerivAt.comp x (by simpa using (hasDerivAt_id' x).const_mul c)
    rw [hd.deriv, mul_comm]
  · have hnd : ¬ DifferentiableAt ℝ (fun t ↦ f (c * t)) x := by
      intro hdg
      refine hdiff ?_
      let g : ℝ → ℝ := fun t ↦ f (c * t)
      have hdg' : DifferentiableAt ℝ g (c⁻¹ * (c * x)) := by
        simpa [g, inv_mul_cancel_left₀ hc] using hdg
      have hd_inv : DifferentiableAt ℝ (g ∘ fun y ↦ c⁻¹ * y) (c * x) :=
        DifferentiableAt.comp (g := g) (f := fun y ↦ c⁻¹ * y) (c * x) hdg'
          (differentiableAt_id.const_mul c⁻¹)
      refine hd_inv.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
      dsimp only [Function.comp_apply, g]
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hdiff, mul_zero]

/-- Positive scaling of equilibrium variables (`SteinIntro.tex:2894`; `ISSUE-5.4`). -/
theorem IsEquilibrium.const_mul_pos {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ℝ} {Xe : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c) (hEq : IsEquilibrium P X P' Xe) :
    IsEquilibrium P (fun ω ↦ c * X ω) P' (fun ω' ↦ c * Xe ω') := by
  rcases hEq with ⟨hX_nn, hX_int, hXe_aem, hEq_id⟩
  refine ⟨hX_nn.mono fun _ hω ↦ mul_nonneg hc.le hω, hX_int.const_mul c,
    hXe_aem.const_mul c, fun f ⟨K, hLip⟩ ↦ ?_⟩
  let g : ℝ → ℝ := fun t ↦ f (c * t)
  have hg_lip : LipschitzWith (Real.toNNReal c * K) g := by
    refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul, Real.coe_toNNReal c hc.le]
    have hd := hLip.dist_le_mul (c * u) (c * v)
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc] at hd
    linarith
  have h := hEq_id g ⟨Real.toNNReal c * K, hg_lip⟩
  have hg0 : g 0 = f 0 := by simp [g]
  have hder : (fun ω' ↦ deriv g (Xe ω')) = fun ω' ↦ c * deriv f (c * Xe ω') :=
    funext fun ω' ↦ deriv_comp_mul_left_eq' f hc.ne' (Xe ω')
  rw [hg0, hder, integral_const_mul] at h
  dsimp only [g] at h
  rw [h, integral_const_mul]
  ring

/-- **Section 5.1 equilibrium scaling, restricted to $c > 0$** (`SteinIntro.tex:2894`;
`ISSUE-5.4`). -/
theorem sec5_1_equilibrium_scale_restricted
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xe : Ω' → ℝ} {c : ℝ} (hc : 0 < c) :
    IsEquilibrium P X P' Xe ↔
      IsEquilibrium P (fun ω ↦ c * X ω) P' (fun ω' ↦ c * Xe ω') := by
  refine ⟨fun h ↦ h.const_mul_pos hc, fun h ↦ ?_⟩
  have h' := h.const_mul_pos (inv_pos.mpr hc)
  simpa [inv_mul_cancel_left₀ hc.ne'] using h'

end SteinMethod
