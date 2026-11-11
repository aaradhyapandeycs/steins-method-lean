/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Kolmogorov.BinomialUpper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Binomial Normal Approximation Order in Kolmogorov and Wasserstein Metrics

Completes the proof of the Section 3.6 motivating quantitative claim (`Sec3_6_binomial_order`,
`SteinIntro.tex:1655-1657`) of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`), combining the upper bounds in `Formalization.Kolmogorov.BinomialUpper` with
matching $\Omega(n^{-1/2})$ lower bounds:

* `le_binomial_wassersteinDist`: lower bound
  $c_{\mathrm{W}}\, n^{-1/2} \le d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))$ via a smooth
  $1$-Lipschitz periodic cosine test function vanishing on the standardized binomial lattice.
* `le_binomial_kolmogorovDist`: lower bound
  $c_{\mathrm{K}}\, n^{-1/2} \le d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z))$ via Chebyshev
  concentration, pigeonhole over lattice points in $[-2, 2]$, and Lipschitz continuity of $\Phi$.
* `binomial_kolmogorovDist_and_wassersteinDist_order`: two-sided $n^{-1/2}$ order for both
  $d_{\mathrm{K}}$ and $d_{\mathrm{W}}$ for all $n \ge 1$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

section Helpers

private lemma cos_nat_mul_two_pi (k : ℕ) : Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hmul :
        ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      push_cast; ring
    rw [hmul, Real.cos_add_two_pi, ih]

private lemma hasDerivAt_mul_sub_const (t w₀ x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ t * (y - w₀)) t x := by
  simpa only [mul_one, id_eq] using ((hasDerivAt_id x).sub_const w₀).const_mul t

end Helpers

/-! ### Section 1: Wasserstein Lower Bound (`le_binomial_wassersteinDist`) -/

/-- Quantitative Wasserstein-1 lower bound of order $n^{-1/2}$ for standardized $\mathrm{Bin}(n,p)$
(`SteinIntro.tex:1655-1657`). -/
theorem le_binomial_wassersteinDist
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hn : 1 ≤ n) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (_hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let σ₀ : ℝ := Real.sqrt (p * (1 - p))
    let L : ℝ := 2 / (Real.pi * σ₀)
    let W : Ω → ℝ :=
      fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
    ENNReal.ofReal ((stdNormalPDF L * L / (4 * Real.pi * σ₀)) * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤
      wassersteinDist (P.map W) (P'.map Z) := by
  intro σ₀ L W
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpq
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrt_n_ge_one : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (Nat.one_le_cast.mpr hn : (1 : ℝ) ≤ (n : ℝ))
  let s : ℝ := Real.sqrt ((n : ℝ) * p * (1 - p))
  have hs_eq : s = Real.sqrt n * σ₀ := by
    dsimp [s, σ₀]; rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg n)]
  have hs_pos : 0 < s := by rw [hs_eq]; positivity
  let δ : ℝ := 1 / s
  have hδ_pos : 0 < δ := by positivity
  let t : ℝ := 2 * Real.pi / δ
  have ht_pos : 0 < t := by positivity
  have ht_eq : t = 2 * Real.pi * Real.sqrt n * σ₀ := by
    dsimp [t, δ]; rw [hs_eq]; field_simp [hsqrt_n_pos.ne', hσ₀_pos.ne']
  let w₀ : ℝ := -(n : ℝ) * p / s
  let h : ℝ → ℝ := fun x ↦ (δ / (2 * Real.pi)) * (1 - Real.cos (t * (x - w₀)))
  have hh_deriv : ∀ x : ℝ, HasDerivAt h (Real.sin (t * (x - w₀))) x := fun x ↦ by
    have hlin := hasDerivAt_mul_sub_const t w₀ x
    have hsub : HasDerivAt (fun y : ℝ ↦ 1 - Real.cos (t * (y - w₀)))
        (Real.sin (t * (x - w₀)) * t) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub hlin.cos
    have hmul := hsub.const_mul (δ / (2 * Real.pi))
    have hval : (δ / (2 * Real.pi)) * (Real.sin (t * (x - w₀)) * t) =
        Real.sin (t * (x - w₀)) := by
      dsimp [t]; field_simp [hδ_pos.ne', Real.pi_ne_zero]
    rwa [hval] at hmul
  have hh_lip : LipschitzWith 1 h := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hh_deriv x).differentiableAt) fun x ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, (hh_deriv x).deriv, NNReal.coe_one]
    exact Real.abs_sin_le_one _
  have hh_nonneg : ∀ x : ℝ, 0 ≤ h x := fun x ↦
    mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  have hh_bdd : ∀ x : ℝ, |h x| ≤ δ / Real.pi := fun x ↦ by
    rw [abs_of_nonneg (hh_nonneg x)]
    have hle2 : 1 - Real.cos (t * (x - w₀)) ≤ 2 := by
      linarith [Real.neg_one_le_cos (t * (x - w₀))]
    calc (δ / (2 * Real.pi)) * (1 - Real.cos (t * (x - w₀)))
        ≤ (δ / (2 * Real.pi)) * 2 := mul_le_mul_of_nonneg_left hle2 (by positivity)
      _ = δ / Real.pi := by field_simp [Real.pi_ne_zero]
  have hW_meas : Measurable W :=
    ((Finset.measurable_fun_sum _ fun i _ ↦ hX_meas i).sub_const _).div_const _
  have : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW_meas.aemeasurable).mpr ‹_›
  have : IsProbabilityMeasure (P'.map Z) := by rw [hZ_law]; infer_instance
  have hh_int_W : Integrable h (P.map W) :=
    memLp_one_iff_integrable.mp
      (memLp_of_ae_abs_le (δ / Real.pi) hh_lip.continuous.measurable (ae_of_all _ hh_bdd) 1)
  have hh_int_Z : Integrable h (P'.map Z) :=
    memLp_one_iff_integrable.mp
      (memLp_of_ae_abs_le (δ / Real.pi) hh_lip.continuous.measurable (ae_of_all _ hh_bdd) 1)
  have hint_W_zero : ∫ x, h x ∂(P.map W) = 0 := by
    rw [integral_map hW_meas.aemeasurable hh_lip.continuous.aestronglyMeasurable]
    have hae_zero : (fun ω ↦ h (W ω)) =ᵐ[P] fun _ ↦ (0 : ℝ) := by
      filter_upwards [ae_all_iff.mpr hX_01] with ω hω
      let k : ℕ := (Finset.univ.filter (fun i : Fin n ↦ X i ω = 1)).card
      have hsum_k : ∑ i : Fin n, X i ω = (k : ℝ) := sum_bernoulli_eq_card_filter hω
      have harg : t * (W ω - w₀) = (k : ℝ) * (2 * Real.pi) := by
        dsimp [W, w₀, t, δ, s] at *
        rw [hsum_k]
        field_simp [hs_pos.ne']
        ring
      dsimp [h]
      rw [harg, cos_nat_mul_two_pi k, sub_self, mul_zero]
    rw [integral_congr_ae hae_zero, integral_const, smul_zero]
  have hL_pos : 0 < L := by dsimp [L]; positivity
  have h2_div_t_le : 2 / t ≤ L / 2 := by
    have htL : 4 ≤ t * L := by
      have h1 : 4 = (2 * Real.pi * 1 * σ₀) * L := by
        dsimp [L]; field_simp [Real.pi_ne_zero, hσ₀_pos.ne']; ring
      have h2 : 2 * Real.pi * 1 * σ₀ ≤ t := by
        rw [ht_eq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt_n_ge_one (by positivity)) hσ₀_pos.le
      calc (4 : ℝ) = (2 * Real.pi * 1 * σ₀) * L := h1
        _ ≤ t * L := mul_le_mul_of_nonneg_right h2 hL_pos.le
    rw [div_le_div_iff₀ ht_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hftc_val : L / 2 ≤ ∫ x in (0 : ℝ)..L, (1 - Real.cos (t * (x - w₀))) := by
    let F : ℝ → ℝ := fun x ↦ x - Real.sin (t * (x - w₀)) / t
    have hF_deriv : ∀ x ∈ uIcc 0 L, HasDerivAt F (1 - Real.cos (t * (x - w₀))) x := by
      intro x _
      have hlin := hasDerivAt_mul_sub_const t w₀ x
      have hsin_div : HasDerivAt (fun y : ℝ ↦ Real.sin (t * (y - w₀)) / t)
          (Real.cos (t * (x - w₀))) x := by
        have hd := hlin.sin.div_const t
        rwa [mul_div_cancel_right₀ _ ht_pos.ne'] at hd
      exact (hasDerivAt_id x).fun_sub hsin_div
    have hcont_int : Continuous (fun x : ℝ ↦ 1 - Real.cos (t * (x - w₀))) := by fun_prop
    have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
      (hcont_int.intervalIntegrable 0 L)
    have hsin_diff :
        (Real.sin (t * (L - w₀)) - Real.sin (t * (0 - w₀))) / t ≤ 2 / t := by
      refine div_le_div_of_nonneg_right ?_ ht_pos.le
      linarith [Real.sin_le_one (t * (L - w₀)), Real.neg_one_le_sin (t * (0 - w₀))]
    have hF_sub : F L - F 0 = L - (Real.sin (t * (L - w₀)) - Real.sin (t * (0 - w₀))) / t := by
      dsimp [F]; ring
    rw [heval, hF_sub]
    linarith
  have hint_Z_ge :
      (stdNormalPDF L * L / (4 * Real.pi * σ₀)) * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ∫ x, h x ∂(P'.map Z) := by
    rw [hZ_law]
    have hexp_eq : ∫ x, h x ∂stdNormalLaw = ∫ x, stdNormalPDF x * h x :=
      stdNormalExpect_eq_integral_mul_pdf h
    rw [hexp_eq]
    have hpdf_int : Integrable (fun x ↦ stdNormalPDF x * h x) volume := by
      refine integrable_stdNormalLaw_iff.mp ?_
      simpa [hZ_law] using hh_int_Z
    let g : ℝ → ℝ := (Ioc 0 L).indicator (fun x ↦ stdNormalPDF L * h x)
    have hg_int : Integrable g volume := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact (hh_lip.continuous.const_mul (stdNormalPDF L)).integrableOn_Ioc
    have hg_le : ∀ x : ℝ, g x ≤ stdNormalPDF x * h x := fun x ↦ by
      by_cases hx : x ∈ Ioc 0 L
      · simp only [g, indicator_of_mem hx]
        have hx0 : 0 ≤ x := hx.1.le
        have hpdf_ge : stdNormalPDF L ≤ stdNormalPDF x := by
          rw [stdNormalPDF_eq, stdNormalPDF_eq]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have hsq : x ^ 2 ≤ L ^ 2 := sq_le_sq' (by linarith) hx.2
          linarith
        exact mul_le_mul_of_nonneg_right hpdf_ge (hh_nonneg x)
      · simp only [g, indicator_of_notMem hx]
        exact mul_nonneg (stdNormalPDF_nonneg x) (hh_nonneg x)
    have hint_g : ∫ x, g x = stdNormalPDF L * (δ / (2 * Real.pi)) *
        ∫ x in (0 : ℝ)..L, (1 - Real.cos (t * (x - w₀))) := by
      rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL_pos.le]
      have hfactor : (fun x : ℝ ↦ stdNormalPDF L * h x) =
          fun x : ℝ ↦ (stdNormalPDF L * (δ / (2 * Real.pi))) *
            (1 - Real.cos (t * (x - w₀))) := by
        ext x; dsimp [h]; ring
      rw [hfactor, intervalIntegral.integral_const_mul]
    have hpdfL_pos : 0 < stdNormalPDF L := stdNormalPDF_pos L
    calc (stdNormalPDF L * L / (4 * Real.pi * σ₀)) * (n : ℝ) ^ (-(1 : ℝ) / 2)
        = stdNormalPDF L * (δ / (2 * Real.pi)) * (L / 2) := by
            rw [rpow_neg_half_eq_one_div_sqrt]; dsimp [δ]; rw [hs_eq]
            field_simp [Real.pi_ne_zero, hσ₀_pos.ne', hsqrt_n_pos.ne']; ring
      _ ≤ stdNormalPDF L * (δ / (2 * Real.pi)) *
            ∫ x in (0 : ℝ)..L, (1 - Real.cos (t * (x - w₀))) :=
            mul_le_mul_of_nonneg_left hftc_val (by positivity)
      _ = ∫ x, g x := hint_g.symm
      _ ≤ ∫ x, stdNormalPDF x * h x := integral_mono hg_int hpdf_int hg_le
  have habs_ge :
      (stdNormalPDF L * L / (4 * Real.pi * σ₀)) * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
        |(∫ x, h x ∂(P.map W)) - (∫ x, h x ∂(P'.map Z))| := by
    rw [hint_W_zero, zero_sub, abs_neg]
    exact hint_Z_ge.trans (le_abs_self _)
  exact (ENNReal.ofReal_le_ofReal habs_ge).trans (le_ipm hh_lip hh_int_W hh_int_Z)

/-! ### Section 2: Kolmogorov Lower Bound (`le_binomial_kolmogorovDist`) -/

/-- Quantitative Kolmogorov lower bound of order $n^{-1/2}$ for standardized $\mathrm{Bin}(n,p)$
(`SteinIntro.tex:1655-1657`). -/
theorem le_binomial_kolmogorovDist
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hn : 1 ≤ n) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (hX_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hX_prob : ∀ i : Fin n, P.real (X i ⁻¹' {1}) = p)
    (_hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let σ₀ : ℝ := Real.sqrt (p * (1 - p))
    let W : Ω → ℝ :=
      fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
    ENNReal.ofReal ((3 / (16 * (4 * σ₀ + 1))) * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤
      kolmogorovDist (P.map W) (P'.map Z) := by
  intro σ₀ W
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpq
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrt_n_ge_one : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (Nat.one_le_cast.mpr hn : (1 : ℝ) ≤ (n : ℝ))
  obtain ⟨hs_pos, hs_eq, _, hW_meas, _, _, _, _, _, _, hW_L2, hW_sq⟩ :=
    bernoulli_stdSum_props P hp0 hp1 hn hX_meas hX_indep hX_01 hX_prob
  let s : ℝ := Real.sqrt ((n : ℝ) * p * (1 - p))
  -- Step 1: Chebyshev concentration P(|W| ≤ 2) ≥ 3/4
  have hmeas_le2 : MeasurableSet {ω : Ω | |W ω| ≤ 2} :=
    measurableSet_Iic.preimage (continuous_abs.measurable.comp hW_meas)
  have hmeas_gt2 : MeasurableSet {ω : Ω | 2 < |W ω|} :=
    measurableSet_Ioi.preimage (continuous_abs.measurable.comp hW_meas)
  have hprob_gt2 : P.real {ω : Ω | 2 < |W ω|} ≤ 1 / 4 := by
    have hpt : ∀ ω : Ω,
        4 * ({ω' : Ω | 2 < |W ω'|}.indicator (fun _ ↦ (1 : ℝ)) ω) ≤ W ω ^ 2 := by
      intro ω
      by_cases hgt : ω ∈ {ω' : Ω | 2 < |W ω'|}
      · rw [indicator_of_mem hgt, mul_one, ← sq_abs (W ω)]
        have hgt' : 2 < |W ω| := hgt
        nlinarith
      · rw [indicator_of_notMem hgt, mul_zero]
        exact sq_nonneg _
    have hint := integral_mono (μ := P)
      (((integrable_const (1 : ℝ)).indicator hmeas_gt2).const_mul 4) hW_L2.integrable_sq hpt
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hmeas_gt2, smul_eq_mul, mul_one,
      hW_sq] at hint
    linarith
  have hprob_le2 : 3 / 4 ≤ P.real {ω : Ω | |W ω| ≤ 2} := by
    have hpart : (fun _ : Ω ↦ (1 : ℝ)) =
        fun ω ↦ {ω' : Ω | |W ω'| ≤ 2}.indicator (fun _ ↦ (1 : ℝ)) ω +
          {ω' : Ω | 2 < |W ω'|}.indicator (fun _ ↦ (1 : ℝ)) ω := by
      ext ω
      rcases le_or_gt |W ω| 2 with hle | hgt
      · have h1 : ω ∈ {ω' : Ω | |W ω'| ≤ 2} := hle
        have h2 : ω ∉ {ω' : Ω | 2 < |W ω'|} := not_lt.mpr hle
        rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero]
      · have h1 : ω ∉ {ω' : Ω | |W ω'| ≤ 2} := not_le.mpr hgt
        have h2 : ω ∈ {ω' : Ω | 2 < |W ω'|} := hgt
        rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add]
    have hint := congr_arg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂P) hpart
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_add ((integrable_const (1 : ℝ)).indicator hmeas_le2)
        ((integrable_const (1 : ℝ)).indicator hmeas_gt2),
      integral_indicator_const (1 : ℝ) hmeas_le2, integral_indicator_const (1 : ℝ) hmeas_gt2,
      smul_eq_mul, mul_one, smul_eq_mul, mul_one] at hint
    linarith
  -- Step 2: Finite lattice cover and pigeonhole
  let w_lat : ℕ → ℝ := fun k ↦ ((k : ℝ) - (n : ℝ) * p) / s
  let S_lat : Finset ℕ :=
    (Finset.range (n + 1)).filter (fun k ↦ |(k : ℝ) - (n : ℝ) * p| ≤ 2 * s)
  have hmeas_eq_w : ∀ k : ℕ, MeasurableSet {ω : Ω | W ω = w_lat k} := fun k ↦
    hW_meas (measurableSet_singleton (w_lat k))
  have hsum_atoms : 3 / 4 ≤ ∑ k ∈ S_lat, P.real {ω : Ω | W ω = w_lat k} := by
    have hae_cov : ∀ᵐ ω ∂P,
        {ω' : Ω | |W ω'| ≤ 2}.indicator (fun _ ↦ (1 : ℝ)) ω ≤
          ∑ k ∈ S_lat, {ω' : Ω | W ω' = w_lat k}.indicator (fun _ ↦ (1 : ℝ)) ω := by
      filter_upwards [ae_all_iff.mpr hX_01] with ω hω
      have hterm_nn : ∀ k ∈ S_lat,
          0 ≤ {ω' : Ω | W ω' = w_lat k}.indicator (fun _ ↦ (1 : ℝ)) ω := fun k _ ↦ by
        by_cases hwk : ω ∈ {ω' : Ω | W ω' = w_lat k}
        · rw [indicator_of_mem hwk]; exact zero_le_one
        · rw [indicator_of_notMem hwk]
      by_cases hle : ω ∈ {ω' : Ω | |W ω'| ≤ 2}
      · rw [indicator_of_mem hle]
        let k₀ : ℕ := (Finset.univ.filter (fun i : Fin n ↦ X i ω = 1)).card
        have hk₀_le : k₀ ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
        have hsum_k₀ : ∑ i : Fin n, X i ω = (k₀ : ℝ) := sum_bernoulli_eq_card_filter hω
        have hW_k₀ : W ω = w_lat k₀ := by simp [W, w_lat, s, hsum_k₀]
        have hk₀_mem : k₀ ∈ S_lat := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_of_le hk₀_le, ?_⟩
          have habs_div : |(k₀ : ℝ) - (n : ℝ) * p| / s ≤ 2 := by
            have hle' : |W ω| ≤ 2 := hle
            have h1 : |W ω| = |(k₀ : ℝ) - (n : ℝ) * p| / s := by
              rw [hW_k₀]; dsimp [w_lat]; rw [abs_div, abs_of_pos hs_pos]
            linarith
          exact (div_le_iff₀ hs_pos).mp habs_div
        have hsingle := Finset.single_le_sum hterm_nn hk₀_mem
        have hmem_k₀ : ω ∈ {ω' : Ω | W ω' = w_lat k₀} := hW_k₀
        rwa [indicator_of_mem hmem_k₀] at hsingle
      · rw [indicator_of_notMem hle]
        exact Finset.sum_nonneg hterm_nn
    have hint := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hmeas_le2)
      (integrable_finsetSum S_lat fun k _ ↦ (integrable_const (1 : ℝ)).indicator (hmeas_eq_w k))
      hae_cov
    rw [integral_indicator_const (1 : ℝ) hmeas_le2, smul_eq_mul, mul_one,
      integral_finsetSum S_lat fun k _ ↦ (integrable_const (1 : ℝ)).indicator (hmeas_eq_w k)]
        at hint
    have hsum_eq :
        (∑ k ∈ S_lat,
            ∫ ω, {ω' : Ω | W ω' = w_lat k}.indicator (fun _ ↦ (1 : ℝ)) ω ∂P) =
          ∑ k ∈ S_lat, P.real {ω : Ω | W ω = w_lat k} :=
      Finset.sum_congr rfl fun k _ ↦ by
        rw [integral_indicator_const (1 : ℝ) (hmeas_eq_w k), smul_eq_mul, mul_one]
    rw [hsum_eq] at hint
    exact hprob_le2.trans hint
  have hS_ne : S_lat.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hsum_atoms
    linarith
  have hcard_le : (S_lat.card : ℝ) ≤ (4 * σ₀ + 1) * Real.sqrt n := by
    let k₀ : ℕ := S_lat.min' hS_ne
    let k₁ : ℕ := S_lat.max' hS_ne
    have hk₀_le_k₁ : k₀ ≤ k₁ := S_lat.min'_le k₁ (S_lat.max'_mem hS_ne)
    have hsub_Icc : S_lat ⊆ Finset.Icc k₀ k₁ := fun k hk ↦
      Finset.mem_Icc.mpr ⟨S_lat.min'_le k hk, S_lat.le_max' k hk⟩
    have hcard_nat : S_lat.card ≤ k₁ + 1 - k₀ :=
      (Finset.card_le_card hsub_Icc).trans_eq (Nat.card_Icc k₀ k₁)
    have hcast_card : (S_lat.card : ℝ) ≤ (k₁ : ℝ) - (k₀ : ℝ) + 1 := by
      have h1 : (S_lat.card : ℝ) ≤ ((k₁ + 1 - k₀ : ℕ) : ℝ) := Nat.cast_le.mpr hcard_nat
      have h2 : ((k₁ + 1 - k₀ : ℕ) : ℝ) = (k₁ : ℝ) - (k₀ : ℝ) + 1 := by
        rw [Nat.cast_sub (Nat.le_succ_of_le hk₀_le_k₁)]
        push_cast
        ring
      linarith
    have hk₀_abs : |(k₀ : ℝ) - (n : ℝ) * p| ≤ 2 * s :=
      (Finset.mem_filter.mp (S_lat.min'_mem hS_ne)).2
    have hk₁_abs : |(k₁ : ℝ) - (n : ℝ) * p| ≤ 2 * s :=
      (Finset.mem_filter.mp (S_lat.max'_mem hS_ne)).2
    have hdiff_le : (k₁ : ℝ) - (k₀ : ℝ) ≤ 4 * s := by
      linarith [(abs_le.mp hk₀_abs).1, (abs_le.mp hk₁_abs).2]
    calc (S_lat.card : ℝ)
        ≤ 4 * s + 1 := by linarith
      _ = 4 * (Real.sqrt n * σ₀) + 1 := by rw [show s = Real.sqrt n * σ₀ from hs_eq]
      _ ≤ 4 * (Real.sqrt n * σ₀) + Real.sqrt n := by linarith
      _ = (4 * σ₀ + 1) * Real.sqrt n := by ring
  let α : ℝ := (3 / 4) / ((4 * σ₀ + 1) * Real.sqrt n)
  have hα_pos : 0 < α := by dsimp [α]; positivity
  obtain ⟨k, _, hk_prob⟩ : ∃ k ∈ S_lat, α ≤ P.real {ω : Ω | W ω = w_lat k} := by
    by_contra hall
    push Not at hall
    have hlt : ∑ k ∈ S_lat, P.real {ω : Ω | W ω = w_lat k} < ∑ _ ∈ S_lat, α :=
      Finset.sum_lt_sum_of_nonempty hS_ne hall
    have hsum_α : (∑ _ ∈ S_lat, α) ≤ 3 / 4 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc (S_lat.card : ℝ) * α
          ≤ ((4 * σ₀ + 1) * Real.sqrt n) * α := mul_le_mul_of_nonneg_right hcard_le hα_pos.le
        _ = 3 / 4 := by
            dsimp [α]
            have hden_ne : (4 * σ₀ + 1) * Real.sqrt n ≠ 0 := by positivity
            field_simp [hden_ne]
    linarith
  -- Step 3: CDF jump vs Lipschitz normal CDF
  let y : ℝ := w_lat k
  let ε : ℝ := (α / 2) * Real.sqrt (2 * Real.pi)
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW_meas.aemeasurable).mpr ‹_›
  have : IsProbabilityMeasure (P'.map Z) := by rw [hZ_law]; infer_instance
  have hcdf_W : ∀ x : ℝ, (P.map W).real (Iic x) = P.real {ω : Ω | W ω ≤ x} := fun x ↦
    map_measureReal_apply_of_aemeasurable hW_meas.aemeasurable measurableSet_Iic
  have hcdf_Z : ∀ x : ℝ, (P'.map Z).real (Iic x) = stdNormalCDF x := fun x ↦ by
    rw [hZ_law, ← cdf_eq_real stdNormalLaw x]
  have hjump_W : α ≤ (P.map W).real (Iic y) - (P.map W).real (Iic (y - ε)) := by
    rw [hcdf_W y, hcdf_W (y - ε)]
    have hm_eq : MeasurableSet {ω : Ω | W ω = y} := hmeas_eq_w k
    have hm_le1 : MeasurableSet {ω : Ω | W ω ≤ y - ε} := hW_meas measurableSet_Iic
    have hm_le2 : MeasurableSet {ω : Ω | W ω ≤ y} := hW_meas measurableSet_Iic
    have hpt : ∀ ω : Ω,
        {ω' : Ω | W ω' = y}.indicator (fun _ ↦ (1 : ℝ)) ω +
          {ω' : Ω | W ω' ≤ y - ε}.indicator (fun _ ↦ (1 : ℝ)) ω ≤
        {ω' : Ω | W ω' ≤ y}.indicator (fun _ ↦ (1 : ℝ)) ω := fun ω ↦ by
      by_cases heq : ω ∈ {ω' : Ω | W ω' = y}
      · have heq' : W ω = y := heq
        have hnot : ω ∉ {ω' : Ω | W ω' ≤ y - ε} := fun h ↦ by
          have h' : W ω ≤ y - ε := h
          linarith
        have hle2 : ω ∈ {ω' : Ω | W ω' ≤ y} := heq'.le
        rw [indicator_of_mem heq, indicator_of_notMem hnot, indicator_of_mem hle2, add_zero]
      · rw [indicator_of_notMem heq, zero_add]
        by_cases hle1 : ω ∈ {ω' : Ω | W ω' ≤ y - ε}
        · have hle1' : W ω ≤ y - ε := hle1
          have hle2 : ω ∈ {ω' : Ω | W ω' ≤ y} := by change W ω ≤ y; linarith
          rw [indicator_of_mem hle1, indicator_of_mem hle2]
        · rw [indicator_of_notMem hle1]
          by_cases hle2 : ω ∈ {ω' : Ω | W ω' ≤ y}
          · rw [indicator_of_mem hle2]; exact zero_le_one
          · rw [indicator_of_notMem hle2]
    have hint := integral_mono (μ := P)
      (((integrable_const (1 : ℝ)).indicator hm_eq).add
        ((integrable_const (1 : ℝ)).indicator hm_le1))
      ((integrable_const (1 : ℝ)).indicator hm_le2) hpt
    dsimp only [Pi.add_apply] at hint
    rw [integral_add ((integrable_const (1 : ℝ)).indicator hm_eq)
          ((integrable_const (1 : ℝ)).indicator hm_le1),
        integral_indicator_const (1 : ℝ) hm_eq, integral_indicator_const (1 : ℝ) hm_le1,
        integral_indicator_const (1 : ℝ) hm_le2,
        smul_eq_mul, mul_one, smul_eq_mul, mul_one, smul_eq_mul, mul_one] at hint
    linarith
  have hlip_Z : stdNormalCDF y - stdNormalCDF (y - ε) ≤ α / 2 := by
    have h1 := (le_abs_self _).trans (abs_stdNormalCDF_sub_le (y - ε) y)
    have hdiff : |y - (y - ε)| / Real.sqrt (2 * Real.pi) = α / 2 := by
      have hsub : y - (y - ε) = ε := by ring
      rw [hsub, abs_of_pos hε_pos]; dsimp [ε]
      have h2pi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      field_simp [h2pi]
    linarith
  have hex_x : ∃ x : ℝ, α / 4 ≤ |(P.map W).real (Iic x) - (P'.map Z).real (Iic x)| := by
    by_contra hall
    push Not at hall
    have h1 := hall y
    have h2 := hall (y - ε)
    rw [hcdf_Z y] at h1
    rw [hcdf_Z (y - ε)] at h2
    linarith [(abs_lt.mp h1).2, (abs_lt.mp h2).1]
  obtain ⟨x₀, hx₀⟩ := hex_x
  rw [kolmogorovDist_eq_iSup]
  have hα_div4 : α / 4 = (3 / (16 * (4 * σ₀ + 1))) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [rpow_neg_half_eq_one_div_sqrt]; dsimp [α]
    have hfac : 4 * σ₀ + 1 ≠ 0 := by positivity
    field_simp [hfac, hsqrt_n_pos.ne']; ring
  rw [← hα_div4]
  exact (ENNReal.ofReal_le_ofReal hx₀).trans
    (le_iSup
      (fun x : ℝ ↦ ENNReal.ofReal |(P.map W).real (Iic x) - (P'.map Z).real (Iic x)|) x₀)

/-! ### Section 3: Two-Sided Binomial Rate Assembly (`Sec3_6_binomial_order`) -/

/-- **Section 3.6 Motivating Binomial Rate Claim** (`Sec3_6_binomial_order`,
`SteinIntro.tex:1655-1657`): for fixed $0 < p < 1$, if $W$ is a standardized $\mathrm{Bin}(n,p)$
random variable ($n \ge 1$) and $Z \sim \mathcal{N}(0,1)$, then both
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z))$ and
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))$ have two-sided order $n^{-1/2}$. -/
theorem binomial_kolmogorovDist_and_wassersteinDist_order
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
        1 ≤ n →
        (∀ i : Fin n, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X P →
        (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
        (∀ i : Fin n, P.real (X i ⁻¹' {1}) = p) →
        AEMeasurable Z P' →
        P'.map Z = stdNormalLaw →
        let W : Ω → ℝ :=
          fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
        (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤
            kolmogorovDist (P.map W) (P'.map Z) ∧
          kolmogorovDist (P.map W) (P'.map Z) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2))) ∧
        (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤
            wassersteinDist (P.map W) (P'.map Z) ∧
          wassersteinDist (P.map W) (P'.map Z) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2))) := by
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  let σ₀ : ℝ := Real.sqrt (p * (1 - p))
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpq
  let L : ℝ := 2 / (Real.pi * σ₀)
  have hL_pos : 0 < L := by dsimp [L]; positivity
  have hpdfL_pos : 0 < stdNormalPDF L := stdNormalPDF_pos L
  let c_K : ℝ := 3 / (16 * (4 * σ₀ + 1))
  let c_W : ℝ := stdNormalPDF L * L / (4 * Real.pi * σ₀)
  let C_K : ℝ := (1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 / σ₀)
  let C_W : ℝ := 1 / σ₀ ^ 3 + Real.sqrt 2 / (Real.sqrt Real.pi * σ₀ ^ 2)
  have hc_K : 0 < c_K := by dsimp [c_K]; positivity
  have hc_W : 0 < c_W := by dsimp [c_W]; positivity
  have hC_K : 0 < C_K := by dsimp [C_K]; positivity
  have hC_W : 0 < C_W := by dsimp [C_W]; positivity
  refine ⟨min c_K c_W, max C_K C_W, lt_min hc_K hc_W, lt_max_of_lt_left hC_K, ?_⟩
  intro Ω Ω' _ _ P _ P' _ n X Z hn hX_meas hX_indep hX_01 hX_prob hZ hZ_law W
  have hrpow_nn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hK_lo := le_binomial_kolmogorovDist hp0 hp1 P P' hn hX_meas hX_indep hX_01 hX_prob
    hZ hZ_law
  have hK_hi := binomial_kolmogorovDist_le hp0 hp1 P P' hn hX_meas hX_indep hX_01 hX_prob
    hZ hZ_law
  have hW_lo := le_binomial_wassersteinDist hp0 hp1 P P' hn hX_meas hX_01 hZ hZ_law
  have hW_hi := binomial_wassersteinDist_le hp0 hp1 P P' hn hX_meas hX_indep hX_01 hX_prob
    hZ hZ_law
  dsimp only at hK_lo hK_hi hW_lo hW_hi
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left c_K c_W) hrpow_nn)).trans hK_lo
  · exact hK_hi.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C_K C_W) hrpow_nn))
  · exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_right c_K c_W) hrpow_nn)).trans hW_lo
  · exact hW_hi.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right C_K C_W) hrpow_nn))

end SteinMethod
