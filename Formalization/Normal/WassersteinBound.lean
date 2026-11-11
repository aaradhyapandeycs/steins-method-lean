/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Metrics
import Formalization.Defs.NormalStein
import Formalization.Metrics.Basic
import Formalization.Normal.MillRatio
import Formalization.Normal.SolutionBounds
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Wasserstein Normal Approximation Bounds (`Formalization.Normal.WassersteinBound`)

Proves the two general Wasserstein normal approximation theorems opening Section 3 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:700-735`):

* `kolmogorovDist_map_le_stdNormal_rpow_wassersteinDist_map` (`Sec3_dK_le_dW`,
  `SteinIntro.tex:703-707`): the normal specialization
  $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  (2/\pi)^{1/4} d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))^{1/2}$ of Proposition 1.2(2)
  (`\label{prop22}`, `SteinIntro.tex:527-531`).
* `wassersteinDist_map_stdNormal_le_iSup_normalSteinOp` (**Theorem 3.1**, `\label{thm31}`,
  eq. `(3.2)` `\label{35}`, `SteinIntro.tex:719-724`; ruling `D6` literal smooth class):
  $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \sup_{f \in \mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]|$, proved without moment assumptions on $W$
  by Steklov interval-average smoothing of $1$-Lipschitz test functions combined with Lemma 2.5(2)
  (`\label{lem31}` `\label{i32}`, `SteinIntro.tex:690-694`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Section 1: Kolmogorov–Wasserstein Normal Comparison (`Sec3_dK_le_dW`) -/

/-- **Section 3 Kolmogorov–Wasserstein Normal Comparison** (`SteinIntro.tex:703-707`, specializing
Proposition 1.2(2) `\label{prop22}`, `SteinIntro.tex:527-531`): for any `P`-a.e. measurable
random variable `W` and any `P'`-a.e. measurable `Z` with standard normal law
`P'.map Z = stdNormalLaw`,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
(2 / \pi)^{1/4} d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))^{1/2}$. -/
theorem kolmogorovDist_map_le_stdNormal_rpow_wassersteinDist_map
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (hW : AEMeasurable W P) (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) *
        wassersteinDist (P.map W) (P'.map Z) ^ (1 / 2 : ℝ) := by
  have hZ_dens : P'.map Z = volume.withDensity (gaussianPDF 0 1) := by
    rw [hZ_law, stdNormalLaw, gaussianReal_of_var_ne_zero 0 one_ne_zero]
  have hf : ∀ᵐ x ∂volume,
      gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ :=
    Filter.Eventually.of_forall fun x ↦ by
      rw [gaussianPDF]
      exact ENNReal.ofReal_le_ofReal ((stdNormalPDF_le_zero x).trans_eq stdNormalPDF_zero)
  have hconst_real :
      (2 * (Real.sqrt (2 * Real.pi))⁻¹) ^ (1 / 2 : ℝ) = (2 / Real.pi) ^ (1 / 4 : ℝ) := by
    have hsqrt : 2 * (Real.sqrt (2 * Real.pi))⁻¹ = Real.sqrt (2 / Real.pi) := by
      symm
      rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), mul_pow, inv_pow,
        Real.sq_sqrt (by positivity), ← div_eq_mul_inv,
        div_eq_div_iff Real.pi_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
      ring
    rw [hsqrt, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    congr 1
    norm_num
  have hconst_enn :
      (2 * ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) := by
    have h2C :
        (2 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ =
          ENNReal.ofReal (2 * (Real.sqrt (2 * Real.pi))⁻¹) := by
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat 2]
    rw [h2C, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      hconst_real]
  calc
    kolmogorovDist (P.map W) (P'.map Z)
      ≤ (2 * ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ *
          wassersteinDist (P.map W) (P'.map Z)) ^ (1 / 2 : ℝ) :=
        @kolmogorovDist_le_rpow_wassersteinDist (P.map W) (P'.map Z)
          ((Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›)
          ((Measure.isProbabilityMeasure_map_iff hZ).mpr ‹_›)
          (Real.sqrt (2 * Real.pi))⁻¹ (gaussianPDF 0 1) hZ_dens hf
    _ = (2 * ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹) ^ (1 / 2 : ℝ) *
          wassersteinDist (P.map W) (P'.map Z) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ = ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) *
          wassersteinDist (P.map W) (P'.map Z) ^ (1 / 2 : ℝ) := by
        rw [hconst_enn]

/-! ### Section 2: Steklov Smoothing and Theorem 3.1 (`Thm3_1`) -/

private noncomputable def steklovAvg (h : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  (2 * ε)⁻¹ * ∫ t in (x - ε)..(x + ε), h t

private lemma abs_sub_le_of_lipschitzWith_one {h : ℝ → ℝ} (hh : LipschitzWith 1 h) (u v : ℝ) :
    |h u - h v| ≤ |u - v| := by
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hh.dist_le_mul u v

private lemma hasDerivAt_steklovAvg {h : ℝ → ℝ} (hh_cont : Continuous h) (ε x : ℝ) :
    HasDerivAt (steklovAvg h ε) ((2 * ε)⁻¹ * (h (x + ε) - h (x - ε))) x := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, h t) (h u) u := fun u ↦
    intervalIntegral.integral_hasDerivAt_right (hh_cont.intervalIntegrable 0 u)
      hh_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hh_cont.continuousAt
  have heq : steklovAvg h ε = fun y ↦
      (2 * ε)⁻¹ * ((∫ t in (0 : ℝ)..(y + ε), h t) - ∫ t in (0 : ℝ)..(y - ε), h t) := by
    ext y
    rw [steklovAvg,
      intervalIntegral.integral_interval_sub_left (hh_cont.intervalIntegrable 0 (y + ε))
        (hh_cont.intervalIntegrable 0 (y - ε))]
  rw [heq]
  exact ((HasDerivAt.comp_add_const x ε (hF (x + ε))).fun_sub
    (HasDerivAt.comp_sub_const x ε (hF (x - ε)))).const_mul (2 * ε)⁻¹

private lemma differentiable_steklovAvg {h : ℝ → ℝ} (hh_cont : Continuous h) (ε : ℝ) :
    Differentiable ℝ (steklovAvg h ε) :=
  fun x ↦ (hasDerivAt_steklovAvg hh_cont ε x).differentiableAt

private lemma deriv_steklovAvg {h : ℝ → ℝ} (hh_cont : Continuous h) (ε : ℝ) :
    deriv (steklovAvg h ε) = fun x ↦ (2 * ε)⁻¹ * (h (x + ε) - h (x - ε)) :=
  funext fun x ↦ (hasDerivAt_steklovAvg hh_cont ε x).deriv

private lemma locallyAC_steklovAvg {h : ℝ → ℝ} (hh_cont : Continuous h) (ε a b : ℝ) :
    AbsolutelyContinuousOnInterval (steklovAvg h ε) a b := by
  have hcd : ContDiff ℝ 1 (steklovAvg h ε) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨differentiable_steklovAvg hh_cont ε, ?_⟩
    rw [deriv_steklovAvg hh_cont ε]
    exact continuous_const.mul
      ((hh_cont.comp (continuous_id.add continuous_const)).sub
        (hh_cont.comp (continuous_id.sub continuous_const)))
  exact hcd.contDiffOn.absolutelyContinuousOnInterval

private lemma abs_deriv_steklovAvg_le_one {h : ℝ → ℝ} (hh : LipschitzWith 1 h)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |deriv (steklovAvg h ε) x| ≤ 1 := by
  have hd : |h (x + ε) - h (x - ε)| ≤ 2 * ε := by
    have hlip := abs_sub_le_of_lipschitzWith_one hh (x + ε) (x - ε)
    have hsub : (x + ε) - (x - ε) = 2 * ε := by ring
    rwa [hsub, abs_of_pos (by positivity : 0 < 2 * ε)] at hlip
  rw [congr_fun (deriv_steklovAvg hh.continuous ε) x, abs_mul,
    abs_of_pos (by positivity : 0 < (2 * ε)⁻¹)]
  calc
    (2 * ε)⁻¹ * |h (x + ε) - h (x - ε)|
      ≤ (2 * ε)⁻¹ * (2 * ε) :=
        mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ (2 * ε)⁻¹)
    _ = 1 := inv_mul_cancel₀ (by positivity : 2 * ε ≠ 0)

private lemma abs_steklovAvg_sub_le {h : ℝ → ℝ} (hh : LipschitzWith 1 h)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |steklovAvg h ε x - h x| ≤ ε := by
  have hint_h : IntervalIntegrable h volume (x - ε) (x + ε) :=
    hh.continuous.intervalIntegrable (x - ε) (x + ε)
  have hint_c : IntervalIntegrable (fun _ : ℝ ↦ h x) volume (x - ε) (x + ε) :=
    continuous_const.intervalIntegrable (x - ε) (x + ε)
  have hdiff : steklovAvg h ε x - h x =
      (2 * ε)⁻¹ * ∫ t in (x - ε)..(x + ε), (h t - h x) := by
    have hconst : (2 * ε)⁻¹ * (∫ _ in (x - ε)..(x + ε), h x) = h x := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hsub : (x + ε) - (x - ε) = 2 * ε := by ring
      rw [hsub, ← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * ε ≠ 0), one_mul]
    calc
      steklovAvg h ε x - h x
        = (2 * ε)⁻¹ * (∫ t in (x - ε)..(x + ε), h t) -
            (2 * ε)⁻¹ * (∫ _ in (x - ε)..(x + ε), h x) := by rw [steklovAvg, hconst]
      _ = (2 * ε)⁻¹ * ((∫ t in (x - ε)..(x + ε), h t) -
            ∫ _ in (x - ε)..(x + ε), h x) := by ring
      _ = (2 * ε)⁻¹ * ∫ t in (x - ε)..(x + ε), (h t - h x) := by
          rw [← intervalIntegral.integral_sub hint_h hint_c]
  have hint_le : |∫ t in (x - ε)..(x + ε), (h t - h x)| ≤ ε * (2 * ε) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x - ε) (b := x + ε) (C := ε) (f := fun t ↦ h t - h x) fun t ht ↦ by
        rw [Set.uIoc_of_le (by linarith : x - ε ≤ x + ε)] at ht
        rw [Real.norm_eq_abs]
        exact (abs_sub_le_of_lipschitzWith_one hh t x).trans
          (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hsub : (x + ε) - (x - ε) = 2 * ε := by ring
    rwa [Real.norm_eq_abs, hsub, abs_of_pos (by positivity : 0 < 2 * ε)] at hnorm
  rw [hdiff, abs_mul, abs_of_pos (by positivity : 0 < (2 * ε)⁻¹)]
  calc
    (2 * ε)⁻¹ * |∫ t in (x - ε)..(x + ε), (h t - h x)|
      ≤ (2 * ε)⁻¹ * (ε * (2 * ε)) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity : 0 ≤ (2 * ε)⁻¹)
    _ = ((2 * ε)⁻¹ * (2 * ε)) * ε := by ring
    _ = ε := by rw [inv_mul_cancel₀ (by positivity : 2 * ε ≠ 0), one_mul]

private lemma integrable_and_abs_integral_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h g : ℝ → ℝ} {ε : ℝ} (hh_cont : Continuous h) (hInt : Integrable h μ)
    (hg_cont : Continuous g) (hclose : ∀ x : ℝ, |g x - h x| ≤ ε) :
    Integrable g μ ∧ |(∫ x, g x ∂μ) - (∫ x, h x ∂μ)| ≤ ε := by
  have hInt_diff : Integrable (fun x ↦ g x - h x) μ :=
    Integrable.of_bound (hg_cont.sub hh_cont).aestronglyMeasurable ε
      (ae_of_all μ fun x ↦ by
        rw [Real.norm_eq_abs]
        exact hclose x)
  have hInt_g : Integrable g μ := by
    have hg_eq : g = fun x ↦ h x + (g x - h x) :=
      funext fun x ↦ (add_sub_cancel (h x) (g x)).symm
    rw [hg_eq]
    exact hInt.add hInt_diff
  refine ⟨hInt_g, ?_⟩
  rw [← integral_sub hInt_g hInt, ← Real.norm_eq_abs]
  have hnorm := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x ↦ g x - h x) (C := ε)
    (ae_of_all μ fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hclose x)
  rwa [probReal_univ, mul_one] at hnorm

private lemma normalSteinSol_mem_normalWassersteinClass {g : ℝ → ℝ}
    (hg_diff : Differentiable ℝ g)
    (hg_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b)
    (hg_deriv_le : ∀ t : ℝ, |deriv g t| ≤ 1)
    (hg_int : Integrable g stdNormalLaw) :
    normalSteinSol g ∈ normalWassersteinClass := by
  have hf_diff : Differentiable ℝ (normalSteinSol g) :=
    fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hg_int hg_diff.continuous w).differentiableAt
  have hderiv_eq : deriv (normalSteinSol g) =
      fun w ↦ w * normalSteinSol g w + g w - stdNormalExpect g :=
    funext fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hg_int hg_diff.continuous w).deriv
  have hdf_diff : Differentiable ℝ (deriv (normalSteinSol g)) := by
    rw [hderiv_eq]
    exact ((differentiable_fun_id.fun_mul hf_diff).fun_add hg_diff).sub_const (stdNormalExpect g)
  refine ⟨hf_diff, hdf_diff, ?_, ?_, ?_⟩
  · intro w
    simpa only [mul_one] using abs_normalSteinSol_le_of_lipschitzDeriv hg_ac hg_deriv_le w
  · intro w
    simpa only [mul_one] using abs_deriv_normalSteinSol_le_of_lipschitzDeriv hg_ac hg_deriv_le w
  · intro w
    simpa only [mul_one] using
      abs_iteratedDeriv_two_normalSteinSol_le_of_lipschitzDeriv hg_ac hg_deriv_le w

private lemma normalSteinOp_normalSteinSol_of_continuous {g : ℝ → ℝ}
    (hg_int : Integrable g stdNormalLaw) (hg_cont : Continuous g) (w : ℝ) :
    normalSteinOp (normalSteinSol g) w = g w - stdNormalExpect g := by
  have halg : ∀ a b c : ℝ, (a + b - c) - a = b - c := fun _ _ _ ↦ by ring
  unfold normalSteinOp
  rw [(hasDerivAt_normalSteinSol_of_continuous hg_int hg_cont w).deriv]
  exact halg (w * normalSteinSol g w) (g w) (stdNormalExpect g)

private lemma abs_sub_le_abs_sub_add_two_eps {a b a' b' ε : ℝ}
    (ha : |a' - a| ≤ ε) (hb : |b' - b| ≤ ε) :
    |a - b| ≤ |a' - b'| + 2 * ε := by
  have hdecomp : a - b = (a' - b') - (a' - a) + (b' - b) := by ring
  have h1 : |(a' - b') - (a' - a)| ≤ |a' - b'| + |a' - a| := abs_sub _ _
  have h2 : |(a' - b') - (a' - a) + (b' - b)| ≤ |(a' - b') - (a' - a)| + |b' - b| :=
    abs_add_le _ _
  rw [hdecomp]
  linarith

/-- **Theorem 3.1** (`\label{thm31}`, eq. `(3.2)` `\label{35}`, `SteinIntro.tex:719-724`;
ruling `D6` literal smooth class): for any `P`-a.e. measurable real-valued random variable `W`
and any `P'`-a.e. measurable `Z` with standard normal law `P'.map Z = stdNormalLaw`,
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]|$. -/
theorem wassersteinDist_map_stdNormal_le_iSup_normalSteinOp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (hW : AEMeasurable W P) (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    wassersteinDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P| := by
  unfold wassersteinDist
  refine ipm_le fun h hh hIntW hIntZ ↦ ?_
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ_pos _ ↦ ?_
  set ε : ℝ := (δ : ℝ) / 2
  have hε_pos : 0 < ε := div_pos (NNReal.coe_pos.mpr hδ_pos) zero_lt_two
  have h2ε : 2 * ε = (δ : ℝ) := mul_div_cancel₀ (δ : ℝ) two_ne_zero
  have hg_diff : Differentiable ℝ (steklovAvg h ε) := differentiable_steklovAvg hh.continuous ε
  have hg_cont : Continuous (steklovAvg h ε) := hg_diff.continuous
  have hg_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (steklovAvg h ε) a b :=
    locallyAC_steklovAvg hh.continuous ε
  have hg_deriv_le : ∀ t : ℝ, |deriv (steklovAvg h ε) t| ≤ 1 :=
    abs_deriv_steklovAvg_le_one hh hε_pos
  have hg_close : ∀ x : ℝ, |steklovAvg h ε x - h x| ≤ ε :=
    abs_steklovAvg_sub_le hh hε_pos
  have hprobW : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have hprobZ : IsProbabilityMeasure (P'.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ).mpr ‹_›
  obtain ⟨hInt_g_W, hdiff_W⟩ :=
    @integrable_and_abs_integral_sub_le (P.map W) hprobW h (steklovAvg h ε) ε
      hh.continuous hIntW hg_cont hg_close
  obtain ⟨hInt_g_Z, hdiff_Z⟩ :=
    @integrable_and_abs_integral_sub_le (P'.map Z) hprobZ h (steklovAvg h ε) ε
      hh.continuous hIntZ hg_cont hg_close
  have hInt_g_std : Integrable (steklovAvg h ε) stdNormalLaw := by
    rwa [hZ_law] at hInt_g_Z
  have hf_mem : normalSteinSol (steklovAvg h ε) ∈ normalWassersteinClass :=
    normalSteinSol_mem_normalWassersteinClass hg_diff hg_ac hg_deriv_le hInt_g_std
  have hInt_g_comp : Integrable (fun ω ↦ steklovAvg h ε (W ω)) P :=
    (integrable_map_measure hg_cont.aestronglyMeasurable hW).mp hInt_g_W
  have hstein_eq :
      (∫ x, steklovAvg h ε x ∂(P.map W)) - (∫ z, steklovAvg h ε z ∂(P'.map Z)) =
        ∫ ω, normalSteinOp (normalSteinSol (steklovAvg h ε)) (W ω) ∂P := by
    rw [integral_map hW hg_cont.aestronglyMeasurable, hZ_law]
    change (∫ ω, steklovAvg h ε (W ω) ∂P) - stdNormalExpect (steklovAvg h ε) =
      ∫ ω, normalSteinOp (normalSteinSol (steklovAvg h ε)) (W ω) ∂P
    calc
      (∫ ω, steklovAvg h ε (W ω) ∂P) - stdNormalExpect (steklovAvg h ε)
        = (∫ ω, steklovAvg h ε (W ω) ∂P) -
            ∫ _ : Ω, stdNormalExpect (steklovAvg h ε) ∂P := by
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ = ∫ ω, (steklovAvg h ε (W ω) - stdNormalExpect (steklovAvg h ε)) ∂P :=
          (integral_sub hInt_g_comp (integrable_const _)).symm
      _ = ∫ ω, normalSteinOp (normalSteinSol (steklovAvg h ε)) (W ω) ∂P :=
          integral_congr_ae (ae_of_all _ fun ω ↦
            (normalSteinOp_normalSteinSol_of_continuous hInt_g_std hg_cont (W ω)).symm)
  have htri :
      |(∫ x, h x ∂(P.map W)) - (∫ z, h z ∂(P'.map Z))| ≤
        |∫ ω, normalSteinOp (normalSteinSol (steklovAvg h ε)) (W ω) ∂P| + (δ : ℝ) := by
    rw [← hstein_eq, ← h2ε]
    exact abs_sub_le_abs_sub_add_two_eps hdiff_W hdiff_Z
  calc
    ENNReal.ofReal |(∫ x, h x ∂(P.map W)) - (∫ z, h z ∂(P'.map Z))|
      ≤ ENNReal.ofReal
          (|∫ ω, normalSteinOp (normalSteinSol (steklovAvg h ε)) (W ω) ∂P| + (δ : ℝ)) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |∫ ω, normalSteinOp (normalSteinSol (steklovAvg h ε)) (W ω) ∂P| +
          ENNReal.ofReal (δ : ℝ) :=
        ENNReal.ofReal_add (abs_nonneg _) (NNReal.coe_nonneg δ)
    _ ≤ (⨆ f ∈ normalWassersteinClass,
          ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|) + (δ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact add_le_add
          (le_iSup₂_of_le (normalSteinSol (steklovAvg h ε)) hf_mem le_rfl) le_rfl

end SteinMethod
