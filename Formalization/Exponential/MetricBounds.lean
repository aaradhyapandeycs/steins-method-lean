/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Metrics
import Formalization.Exponential.SteinEquation
import Formalization.Metrics.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Exponential Wasserstein & Kolmogorov Stein Bounds (`Formalization.Exponential.MetricBounds`)

Formalizes Theorem 5.3(1) & 5.3(2) (`\label{thm171}`, `SteinIntro.tex:2758-2773`) and the
exponential Kolmogorov–Wasserstein comparison inequality:
* `thm5_3_1` (**Theorem 5.3(1)**): $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \sup_{f \in \mathcal{F}_W} |\mathbb{E}[f'(W) - f(W)]|$ via Steklov smoothing.
* `thm5_3_2` (**Theorem 5.3(2)**): $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \sup_{f \in \mathcal{F}_K} |\mathbb{E}[f'(W) - f(W)]|$ via upper/lower continuous ramps.
* `kolmogorovDist_le_sqrt_two_mul_wassersteinDist_stdExpLaw`:
  $d_{\mathrm{K}}(\mu, \mathrm{Exp}(1)) \le (2\,d_{\mathrm{W}}(\mu, \mathrm{Exp}(1)))^{1/2}$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

private noncomputable def expSteklovAvg (h : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  (2 * ε)⁻¹ * ∫ t in (x - ε)..(x + ε), h t

private lemma hasDerivAt_expSteklovAvg {h : ℝ → ℝ} (hh_cont : Continuous h) (ε x : ℝ) :
    HasDerivAt (expSteklovAvg h ε) ((2 * ε)⁻¹ * (h (x + ε) - h (x - ε))) x := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, h t) (h u) u := fun u ↦
    intervalIntegral.integral_hasDerivAt_right (hh_cont.intervalIntegrable 0 u)
      hh_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hh_cont.continuousAt
  have heq : expSteklovAvg h ε = fun y ↦
      (2 * ε)⁻¹ * ((∫ t in (0 : ℝ)..(y + ε), h t) - ∫ t in (0 : ℝ)..(y - ε), h t) := by
    ext y
    rw [expSteklovAvg,
      intervalIntegral.integral_interval_sub_left (hh_cont.intervalIntegrable 0 (y + ε))
        (hh_cont.intervalIntegrable 0 (y - ε))]
  rw [heq]
  exact ((HasDerivAt.comp_add_const x ε (hF (x + ε))).fun_sub
    (HasDerivAt.comp_sub_const x ε (hF (x - ε)))).const_mul (2 * ε)⁻¹

private lemma abs_expSteklovAvg_sub_le {h : ℝ → ℝ} (hh : LipschitzWith 1 h)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |expSteklovAvg h ε x - h x| ≤ ε := by
  have hint_h : IntervalIntegrable h volume (x - ε) (x + ε) :=
    hh.continuous.intervalIntegrable (x - ε) (x + ε)
  have hint_c : IntervalIntegrable (fun _ : ℝ ↦ h x) volume (x - ε) (x + ε) :=
    continuous_const.intervalIntegrable (x - ε) (x + ε)
  have hconst : (2 * ε)⁻¹ * (∫ _ in (x - ε)..(x + ε), h x) = h x := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have hsub : (x + ε) - (x - ε) = 2 * ε := by ring
    rw [hsub, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hdiff : expSteklovAvg h ε x - h x =
      (2 * ε)⁻¹ * ∫ t in (x - ε)..(x + ε), (h t - h x) := by
    calc
      expSteklovAvg h ε x - h x
        = (2 * ε)⁻¹ * (∫ t in (x - ε)..(x + ε), h t) -
            (2 * ε)⁻¹ * (∫ _ in (x - ε)..(x + ε), h x) := by rw [expSteklovAvg, hconst]
      _ = (2 * ε)⁻¹ * ∫ t in (x - ε)..(x + ε), (h t - h x) := by
          rw [← mul_sub, intervalIntegral.integral_sub hint_h hint_c]
  have hint_le : |∫ t in (x - ε)..(x + ε), (h t - h x)| ≤ ε * (2 * ε) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x - ε) (b := x + ε) (C := ε) (f := fun t ↦ h t - h x) fun t ht ↦ by
        rw [uIoc_of_le (by linarith : x - ε ≤ x + ε)] at ht
        rw [Real.norm_eq_abs]
        have hlip := hh.dist_le_mul t x
        rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at hlip
        exact hlip.trans (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hsub : (x + ε) - (x - ε) = 2 * ε := by ring
    have h2ε_pos : 0 < 2 * ε := by positivity
    rw [Real.norm_eq_abs, hsub, abs_of_pos h2ε_pos] at hnorm
    exact hnorm
  have h2ε_pos : 0 < 2 * ε := by positivity
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr h2ε_pos)]
  calc
    (2 * ε)⁻¹ * |∫ t in (x - ε)..(x + ε), (h t - h x)|
      ≤ (2 * ε)⁻¹ * (ε * (2 * ε)) := mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = ε := by field_simp [hε.ne']

/-- **Theorem 5.3(1)** (`\label{thm171}`, `SteinIntro.tex:2758-2766`; `D6` literal smooth class):
if $W \ge 0$ a.s. has finite mean and $Z \sim \mathrm{Exp}(1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}_W} |\mathbb{E}[f'(W) - f(W)]|$. -/
theorem thm5_3_1 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (_hW_nn : 0 ≤ᵐ[P] W) (hW_int : Integrable W P)
    (_hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdExpLaw) :
    wassersteinDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ expWassersteinClass, ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P| := by
  have hW : AEMeasurable W P := hW_int.aemeasurable
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  rw [hZ_law]
  unfold wassersteinDist
  refine ipm_le fun h hh hIntW hIntZ ↦ ?_
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ_pos _ ↦ ?_
  set ε : ℝ := (δ : ℝ) / 2
  have hε_pos : 0 < ε := div_pos (NNReal.coe_pos.mpr hδ_pos) zero_lt_two
  set g := expSteklovAvg h ε
  have hg_diff : Differentiable ℝ g :=
    fun x ↦ (hasDerivAt_expSteklovAvg hh.continuous ε x).differentiableAt
  have hg_deriv_eq : deriv g = fun x ↦ (2 * ε)⁻¹ * (h (x + ε) - h (x - ε)) :=
    funext fun x ↦ (hasDerivAt_expSteklovAvg hh.continuous ε x).deriv
  have hg_cd1 : ContDiff ℝ 1 g := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hg_diff, ?_⟩
    rw [hg_deriv_eq]
    exact continuous_const.mul
      ((hh.continuous.comp (by fun_prop)).sub (hh.continuous.comp (by fun_prop)))
  have hg_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b :=
    fun a b ↦ hg_cd1.contDiffOn.absolutelyContinuousOnInterval
  have hg_deriv_le : ∀ t : ℝ, |deriv g t| ≤ 1 := by
    intro t
    have h2ε_pos : 0 < 2 * ε := by positivity
    rw [hg_deriv_eq, abs_mul, abs_of_pos (inv_pos.mpr h2ε_pos)]
    have hd := hh.dist_le_mul (t + ε) (t - ε)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at hd
    have hsub : (t + ε) - (t - ε) = 2 * ε := by ring
    rw [hsub, abs_of_pos h2ε_pos] at hd
    calc
      (2 * ε)⁻¹ * |h (t + ε) - h (t - ε)| ≤ (2 * ε)⁻¹ * (2 * ε) :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr h2ε_pos.le)
      _ = 1 := inv_mul_cancel₀ h2ε_pos.ne'
  have hg_close : ∀ x : ℝ, |g x - h x| ≤ ε := abs_expSteklovAvg_sub_le hh hε_pos
  have hInt_g_Z : Integrable g stdExpLaw := by
    have hdiff_int : Integrable (fun x ↦ g x - h x) stdExpLaw :=
      Integrable.of_bound (hg_diff.continuous.sub hh.continuous).aestronglyMeasurable ε
        (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hg_close x)
    have heq : g = fun x ↦ h x + (g x - h x) := funext fun x ↦ by ring
    rw [heq]; exact hIntZ.add hdiff_int
  have hInt_g_W : Integrable g (P.map W) := by
    have hdiff_int : Integrable (fun x ↦ g x - h x) (P.map W) :=
      Integrable.of_bound (hg_diff.continuous.sub hh.continuous).aestronglyMeasurable ε
        (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hg_close x)
    have heq : g = fun x ↦ h x + (g x - h x) := funext fun x ↦ by ring
    rw [heq]; exact hIntW.add hdiff_int
  set f := expSteinSol g
  have hf_ode := (lem5_2_formula.2 hg_diff.continuous hInt_g_Z).1
  have hf_bds := lem5_2_2 hg_ac hg_deriv_le
  have hf_deriv_eq : deriv f = fun x ↦ f x + g x - stdExpExpect g :=
    funext fun x ↦ (hf_ode x).deriv
  have hf_mem : f ∈ expWassersteinClass := by
    refine ⟨hf_bds.1, ?_, fun x ↦ (hf_bds.2.2 x).1, fun x ↦ by simpa using (hf_bds.2.2 x).2,
      expSteinSol_zero hInt_g_Z⟩
    rw [hf_deriv_eq]
    exact (hf_bds.1.add hg_diff).sub_const _
  have hstein_eq : ∫ ω, (deriv f (W ω) - f (W ω)) ∂P =
      (∫ x, g x ∂P.map W) - ∫ x, g x ∂stdExpLaw := by
    have hpt : ∀ u : ℝ, deriv f u - f u = g u - stdExpExpect g := by
      intro u; rw [hf_deriv_eq]; ring
    simp_rw [hpt]
    have hgW_int : Integrable (fun ω ↦ g (W ω)) P :=
      (integrable_map_measure hg_diff.continuous.aestronglyMeasurable hW).mp hInt_g_W
    rw [integral_sub hgW_int (integrable_const _), integral_const, probReal_univ, one_smul,
      integral_map hW hg_diff.continuous.aestronglyMeasurable, stdExpExpect]
  have herr_W : |(∫ x, g x ∂P.map W) - ∫ x, h x ∂P.map W| ≤ ε := by
    rw [← integral_sub hInt_g_W hIntW]
    have hb := norm_integral_le_of_norm_le_const (μ := P.map W) (C := ε)
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hg_close x)
    simpa [Real.norm_eq_abs] using hb
  have herr_Z : |(∫ x, g x ∂stdExpLaw) - ∫ x, h x ∂stdExpLaw| ≤ ε := by
    rw [← integral_sub hInt_g_Z hIntZ]
    have hb := norm_integral_le_of_norm_le_const (μ := stdExpLaw) (C := ε)
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hg_close x)
    simpa [Real.norm_eq_abs] using hb
  have htot : |(∫ x, h x ∂P.map W) - ∫ x, h x ∂stdExpLaw| ≤
      |∫ ω, (deriv f (W ω) - f (W ω)) ∂P| + (δ : ℝ) := by
    rw [hstein_eq]
    have hdecomp : (∫ x, h x ∂P.map W) - (∫ x, h x ∂stdExpLaw) =
        ((∫ x, g x ∂P.map W) - (∫ x, g x ∂stdExpLaw)) -
          ((∫ x, g x ∂P.map W) - (∫ x, h x ∂P.map W)) +
          ((∫ x, g x ∂stdExpLaw) - (∫ x, h x ∂stdExpLaw)) := by ring
    have h2ε : 2 * ε = (δ : ℝ) := mul_div_cancel₀ (δ : ℝ) two_ne_zero
    rw [hdecomp]
    have h1 := abs_add_le
      (((∫ x, g x ∂P.map W) - (∫ x, g x ∂stdExpLaw)) -
        ((∫ x, g x ∂P.map W) - (∫ x, h x ∂P.map W)))
      ((∫ x, g x ∂stdExpLaw) - (∫ x, h x ∂stdExpLaw))
    have h2 := abs_sub ((∫ x, g x ∂P.map W) - (∫ x, g x ∂stdExpLaw))
      ((∫ x, g x ∂P.map W) - (∫ x, h x ∂P.map W))
    linarith
  calc
    ENNReal.ofReal |(∫ x, h x ∂P.map W) - ∫ x, h x ∂stdExpLaw|
      ≤ ENNReal.ofReal (|∫ ω, (deriv f (W ω) - f (W ω)) ∂P| + (δ : ℝ)) :=
        ENNReal.ofReal_le_ofReal htot
    _ = ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P| + ↑δ := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (NNReal.coe_nonneg δ), ENNReal.ofReal_coe_nnreal]
    _ ≤ (⨆ f ∈ expWassersteinClass, ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|) + ↑δ :=
        add_le_add_left (le_biSup (fun f ↦ ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|)
          hf_mem) ↑δ

private noncomputable def expKolmRamp (a δ t : ℝ) : ℝ :=
  max 0 (min 1 (1 - δ⁻¹ * (t - a)))

private lemma continuous_expKolmRamp (a δ : ℝ) : Continuous (expKolmRamp a δ) := by
  unfold expKolmRamp; fun_prop

private lemma expKolmRamp_nonneg (a δ t : ℝ) : 0 ≤ expKolmRamp a δ t :=
  le_max_left 0 _

private lemma expKolmRamp_le_one (a δ t : ℝ) : expKolmRamp a δ t ≤ 1 :=
  max_le zero_le_one (min_le_left 1 _)

private lemma indicator_Iic_le_expKolmRamp {a δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (Iic a).indicator (1 : ℝ → ℝ) t ≤ expKolmRamp a δ t := by
  by_cases ht : t ≤ a
  · have hmem : t ∈ Iic a := ht
    rw [indicator_of_mem hmem, Pi.one_apply]
    have hmul : δ⁻¹ * (t - a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht)
    simp [expKolmRamp, min_eq_left (by linarith : 1 ≤ 1 - δ⁻¹ * (t - a))]
  · have hnot : t ∉ Iic a := ht
    rw [indicator_of_notMem hnot]
    exact expKolmRamp_nonneg a δ t

private lemma expKolmRamp_le_indicator_Iic_add {a δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    expKolmRamp a δ t ≤ (Iic (a + δ)).indicator (1 : ℝ → ℝ) t := by
  by_cases ht : t ≤ a + δ
  · have hmem : t ∈ Iic (a + δ) := ht
    rw [indicator_of_mem hmem, Pi.one_apply]
    exact expKolmRamp_le_one a δ t
  · have hnot : t ∉ Iic (a + δ) := ht
    rw [indicator_of_notMem hnot]
    have hsub : δ < t - a := by linarith
    have hmul : 1 < δ⁻¹ * (t - a) := by
      have := mul_lt_mul_of_pos_left hsub (inv_pos.mpr hδ)
      rwa [inv_mul_cancel₀ hδ.ne'] at this
    exact max_le le_rfl ((min_le_right 1 _).trans (by linarith))

private lemma stdExpLaw_real_Ioc_le {a b : ℝ} (hab : a ≤ b) :
    stdExpLaw.real (Ioc a b) ≤ b - a := by
  change (expLaw 1).real (Ioc a b) ≤ b - a
  rw [measureReal_def, expLaw_eq_withDensity (r := 1), withDensity_apply _ measurableSet_Ioc]
  have hle : ∫⁻ x in Ioc a b, exponentialPDF 1 x ≤ ∫⁻ _ in Ioc a b, (1 : ℝ≥0∞) := by
    refine setLIntegral_mono (by fun_prop) fun x _ ↦ ?_
    rw [exponentialPDF_eq]
    split_ifs with hx
    · rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have : Real.exp (-(1 * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · simp
  rw [setLIntegral_const, one_mul, Real.volume_Ioc] at hle
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
    (ENNReal.toReal_ofReal (sub_nonneg.mpr hab)).le

/-- **Theorem 5.3(2)** (`\label{thm171}`, `SteinIntro.tex:2758-2760, 2767-2772`; `D6` literal
differentiable class): if $W \ge 0$ a.s. has finite mean and $Z \sim \mathrm{Exp}(1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}_K} |\mathbb{E}[f'(W) - f(W)]|$. -/
theorem thm5_3_2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (_hW_nn : 0 ≤ᵐ[P] W) (hW_int : Integrable W P)
    (_hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdExpLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ expKolmogorovClass, ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P| := by
  have hW : AEMeasurable W P := hW_int.aemeasurable
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  rw [hZ_law, kolmogorovDist_eq_iSup]
  set S := ⨆ f ∈ expKolmogorovClass, ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|
  refine iSup_le fun x ↦ ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε_pos _ ↦ ?_
  set δ : ℝ := (ε : ℝ)
  have hδ_pos : 0 < δ := NNReal.coe_pos.mpr hε_pos
  have ramp_stein : ∀ a : ℝ,
      |(∫ u, expKolmRamp a δ u ∂P.map W) - ∫ u, expKolmRamp a δ u ∂stdExpLaw| ≤
        ENNReal.toReal (⨆ f ∈ expKolmogorovClass,
          ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|) ∨ S = ⊤ := by
    intro a
    by_cases htop : S = ⊤
    · exact Or.inr htop
    · left
      set g := expKolmRamp a δ
      have hg_cont : Continuous g := continuous_expKolmRamp a δ
      have hg_int_Z : Integrable g stdExpLaw :=
        Integrable.of_bound hg_cont.aestronglyMeasurable 1
          (ae_of_all _ fun t ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (expKolmRamp_nonneg a δ t)]
            exact expKolmRamp_le_one a δ t)
      set f := expSteinSol g
      have hf_ode := (lem5_2_formula.2 hg_cont hg_int_Z).1
      have hf_bds := lem5_2_1 hg_cont.measurable (expKolmRamp_nonneg a δ) (expKolmRamp_le_one a δ)
      have hf_mem : f ∈ expKolmogorovClass :=
        ⟨fun u ↦ (hf_ode u).differentiableAt, fun u ↦ (hf_bds.2 u).1,
          fun u ↦ by simpa using (hf_bds.2 u).2.1, expSteinSol_zero hg_int_Z⟩
      have hpt : ∀ u : ℝ, deriv f u - f u = g u - stdExpExpect g := by
        intro u; rw [(hf_ode u).deriv]; ring
      have hgW_int : Integrable (fun ω ↦ g (W ω)) P :=
        Integrable.of_bound (hg_cont.measurable.comp_aemeasurable hW).aestronglyMeasurable 1
          (ae_of_all _ fun ω ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (expKolmRamp_nonneg a δ (W ω))]
            exact expKolmRamp_le_one a δ (W ω))
      have hid : ∫ ω, (deriv f (W ω) - f (W ω)) ∂P =
          (∫ u, g u ∂P.map W) - ∫ u, g u ∂stdExpLaw := by
        simp_rw [hpt]
        rw [integral_sub hgW_int (integrable_const _), integral_const, probReal_univ, one_smul,
          integral_map hW hg_cont.aestronglyMeasurable, stdExpExpect]
      rw [← hid]
      have hle_S : ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P| ≤ S :=
        le_biSup (fun f ↦ ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|) hf_mem
      have := ENNReal.toReal_mono htop hle_S
      rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this
  by_cases htop : S = ⊤
  · rw [htop, top_add]; exact le_top
  obtain h_up | h_abs := ramp_stein x
  swap; · exact False.elim (htop h_abs)
  obtain h_lo | h_abs := ramp_stein (x - δ)
  swap; · exact False.elim (htop h_abs)
  have hcdf_upper : (P.map W).real (Iic x) - stdExpLaw.real (Iic x) ≤ S.toReal + δ := by
    have hW_le : (P.map W).real (Iic x) ≤ ∫ u, expKolmRamp x δ u ∂P.map W := by
      rw [← integral_indicator_one measurableSet_Iic]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
        (Integrable.of_bound (continuous_expKolmRamp x δ).aestronglyMeasurable 1
          (ae_of_all _ fun t ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (expKolmRamp_nonneg x δ t)]
            exact expKolmRamp_le_one x δ t))
        (indicator_Iic_le_expKolmRamp hδ_pos)
    have hZ_le : ∫ u, expKolmRamp x δ u ∂stdExpLaw ≤ stdExpLaw.real (Iic (x + δ)) := by
      rw [← integral_indicator_one measurableSet_Iic]
      exact integral_mono
        (Integrable.of_bound (continuous_expKolmRamp x δ).aestronglyMeasurable 1
          (ae_of_all _ fun t ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (expKolmRamp_nonneg x δ t)]
            exact expKolmRamp_le_one x δ t))
        ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
        (expKolmRamp_le_indicator_Iic_add hδ_pos)
    have hZ_split : stdExpLaw.real (Iic (x + δ)) =
        stdExpLaw.real (Iic x) + stdExpLaw.real (Ioc x (x + δ)) := by
      rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
        Iic_union_Ioc_eq_Iic (by linarith)]
    have hZ_band : stdExpLaw.real (Ioc x (x + δ)) ≤ δ := by
      simpa using stdExpLaw_real_Ioc_le (by linarith : x ≤ x + δ)
    linarith [(le_abs_self _).trans h_up]
  have hcdf_lower : stdExpLaw.real (Iic x) - (P.map W).real (Iic x) ≤ S.toReal + δ := by
    have hZ_le : stdExpLaw.real (Iic (x - δ)) ≤ ∫ u, expKolmRamp (x - δ) δ u ∂stdExpLaw := by
      rw [← integral_indicator_one measurableSet_Iic]
      exact integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
        (Integrable.of_bound (continuous_expKolmRamp (x - δ) δ).aestronglyMeasurable 1
          (ae_of_all _ fun t ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (expKolmRamp_nonneg (x - δ) δ t)]
            exact expKolmRamp_le_one (x - δ) δ t))
        (indicator_Iic_le_expKolmRamp hδ_pos)
    have hW_le : ∫ u, expKolmRamp (x - δ) δ u ∂P.map W ≤ (P.map W).real (Iic x) := by
      have hind : (P.map W).real (Iic x) =
          ∫ u, (Iic (x - δ + δ)).indicator 1 u ∂P.map W := by
        rw [sub_add_cancel, integral_indicator_one measurableSet_Iic]
      rw [hind]
      exact integral_mono
        (Integrable.of_bound (continuous_expKolmRamp (x - δ) δ).aestronglyMeasurable 1
          (ae_of_all _ fun t ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (expKolmRamp_nonneg (x - δ) δ t)]
            exact expKolmRamp_le_one (x - δ) δ t))
        ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
        (expKolmRamp_le_indicator_Iic_add hδ_pos)
    have hZ_split : stdExpLaw.real (Iic x) =
        stdExpLaw.real (Iic (x - δ)) + stdExpLaw.real (Ioc (x - δ) x) := by
      rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
        Iic_union_Ioc_eq_Iic (by linarith)]
    have hZ_band : stdExpLaw.real (Ioc (x - δ) x) ≤ δ := by
      simpa using stdExpLaw_real_Ioc_le (by linarith : x - δ ≤ x)
    linarith [(neg_le_abs _).trans h_lo]
  have habs : |(P.map W).real (Iic x) - stdExpLaw.real (Iic x)| ≤ S.toReal + δ :=
    abs_le.mpr ⟨by linarith, hcdf_upper⟩
  calc
    ENNReal.ofReal |(P.map W).real (Iic x) - stdExpLaw.real (Iic x)|
      ≤ ENNReal.ofReal (S.toReal + δ) := ENNReal.ofReal_le_ofReal habs
    _ = ENNReal.ofReal S.toReal + ↑ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ_pos.le, ENNReal.ofReal_coe_nnreal]
    _ = S + ↑ε := by rw [ENNReal.ofReal_toReal htop]

/-- Exponential Kolmogorov–Wasserstein comparison (specializing Proposition 1.2(2)
`\label{prop22}`, `SteinIntro.tex:527-531`, since the density of $\mathrm{Exp}(1)$ is bounded by
$1$): $d_{\mathrm{K}}(\mu, \mathrm{Exp}(1)) \le (2\,d_{\mathrm{W}}(\mu, \mathrm{Exp}(1)))^{1/2}$. -/
theorem kolmogorovDist_le_sqrt_two_mul_wassersteinDist_stdExpLaw
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    kolmogorovDist μ stdExpLaw ≤ (2 * wassersteinDist μ stdExpLaw) ^ (1 / 2 : ℝ) := by
  have hf : ∀ᵐ x ∂volume, exponentialPDF 1 x ≤ ENNReal.ofReal 1 :=
    Eventually.of_forall fun x ↦ by
      rw [exponentialPDF_eq]
      split_ifs with hx
      · refine ENNReal.ofReal_le_ofReal ?_
        have : Real.exp (-(1 * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      · simp
  simpa using @kolmogorovDist_le_rpow_wassersteinDist μ stdExpLaw ‹_› inferInstance 1
    (exponentialPDF 1) (expLaw_eq_withDensity (r := 1)) hf

end SteinMethod
