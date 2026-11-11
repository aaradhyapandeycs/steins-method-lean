/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.ZeroBias
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.CDF

/-!
# Zero-Bias Lebesgue Density and Uniqueness (`Formalization.ZeroBias.Density`)

Proves Proposition 3.19 (`\label{i81}`, `\label{i82}`, eqs. `(3.31)`–`(3.32)` `\label{81}`–
`\label{82}`, `SteinIntro.tex:1471-1515`; `ISSUE-3.10`, `ISSUE-3.19`, ruling `D9`) together with
the sublinear-$C^1$ law-identification criterion `isZeroBias_and_map_eq_of_c1_sublinear` and the
machine-checked $\sigma^2 = 0$ counterexample `Prop3_19_sigma_zero_counterexample`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- Continuity of any function that is absolutely continuous on every compact interval. -/
theorem continuous_of_locallyAC {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  have hcont := (hf (x - 1) (x + 1)).continuousOn
  rw [uIcc_of_le (by linarith)] at hcont
  exact hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- Law invariance of `IsZeroBias` in both arguments (`SteinIntro.tex:1442-1449`). -/
theorem IsZeroBias.congr_identDistrib
    {Ω₁ Ω₂ Ω₁' Ω₂' : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₁'] [MeasurableSpace Ω₂']
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P₁' : Measure Ω₁'} {P₂' : Measure Ω₂'}
    {W₁ : Ω₁ → ℝ} {W₂ : Ω₂ → ℝ} {Wz₁ : Ω₁' → ℝ} {Wz₂ : Ω₂' → ℝ}
    (hZB : IsZeroBias P₁ W₁ P₁' Wz₁)
    (hW : IdentDistrib W₁ W₂ P₁ P₂) (hWz : IdentDistrib Wz₁ Wz₂ P₁' P₂') :
    IsZeroBias P₂ W₂ P₂' Wz₂ := by
  rcases hZB with ⟨hW₁_L2, hW₁_mean, _, hZB_eq⟩
  refine ⟨hW.memLp_snd hW₁_L2, hW.integral_eq.symm.trans hW₁_mean, hWz.aemeasurable_snd, ?_⟩
  intro f hf hW₂f_int hWz₂_int
  have hf_meas : Measurable f := (continuous_of_locallyAC hf).measurable
  have hWf_id : IdentDistrib (fun ω ↦ W₁ ω * f (W₁ ω)) (fun ω ↦ W₂ ω * f (W₂ ω)) P₁ P₂ :=
    hW.comp (measurable_id.mul hf_meas)
  have hWzf_id : IdentDistrib (fun ω' ↦ deriv f (Wz₁ ω')) (fun ω' ↦ deriv f (Wz₂ ω')) P₁' P₂' :=
    hWz.comp (measurable_deriv f)
  rw [← hWf_id.integral_eq, ← hW.variance_eq, ← hWzf_id.integral_eq]
  exact hZB_eq f hf (hWf_id.symm.integrable_snd hW₂f_int) (hWzf_id.symm.integrable_snd hWz₂_int)

section DensityProperties

/-- Left-tail representation $p^z(w) = -\sigma^{-2}\mathbb{E}[W\mathbf{1}_{W \le w}]$ and
nonnegativity of `zeroBiasDensity` (`SteinIntro.tex:1481-1483, 1504-1506`). -/
theorem zeroBiasDensity_left_tail_and_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P) (w : ℝ) :
    zeroBiasDensity P W w =
      -(ProbabilityTheory.variance W P)⁻¹ *
        ∫ ω, W ω * (Iic w).indicator 1 (W ω) ∂P ∧
      0 ≤ zeroBiasDensity P W w := by
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW_aem : AEMeasurable W P := hW2.aemeasurable
  have hind_int : ∀ s : Set ℝ, MeasurableSet s →
      Integrable (fun ω ↦ W ω * s.indicator 1 (W ω)) P := fun s hs ↦ by
    refine hW_int.norm.mono'
      (hW2.aestronglyMeasurable.mul
        ((measurable_one.indicator hs).comp_aemeasurable hW_aem).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ ?_)
    by_cases hω : W ω ∈ s <;> simp [hω]
  have hIic := hind_int (Iic w) measurableSet_Iic
  have hIoi := hind_int (Ioi w) measurableSet_Ioi
  have hsplit : W = fun ω ↦
      W ω * (Iic w).indicator 1 (W ω) + W ω * (Ioi w).indicator 1 (W ω) := by
    ext ω
    rcases le_or_gt (W ω) w with hle | hgt
    · simp [(show W ω ∈ Iic w from hle), (show W ω ∉ Ioi w from not_lt.mpr hle)]
    · simp [(show W ω ∉ Iic w from not_le.mpr hgt), (show W ω ∈ Ioi w from hgt)]
  have hsum0 : (∫ ω, W ω * (Iic w).indicator 1 (W ω) ∂P) +
      (∫ ω, W ω * (Ioi w).indicator 1 (W ω) ∂P) = 0 := by
    rw [← integral_add hIic hIoi, ← hsplit, hMean]
  have hleft : zeroBiasDensity P W w =
      -(ProbabilityTheory.variance W P)⁻¹ *
        ∫ ω, W ω * (Iic w).indicator 1 (W ω) ∂P := by
    unfold zeroBiasDensity
    rw [show (∫ ω, W ω * (Ioi w).indicator 1 (W ω) ∂P) =
      -∫ ω, W ω * (Iic w).indicator 1 (W ω) ∂P by linarith]; ring
  refine ⟨hleft, ?_⟩
  rcases le_or_gt 0 w with hw | hw
  · unfold zeroBiasDensity
    refine mul_nonneg (inv_nonneg.mpr hVar.le) (integral_nonneg fun ω ↦ ?_)
    by_cases hgt : w < W ω
    · rw [indicator_of_mem (show W ω ∈ Ioi w from hgt), Pi.one_apply, mul_one]
      exact hw.trans hgt.le
    · simp [show W ω ∉ Ioi w from hgt]
  · rw [show zeroBiasDensity P W w = (ProbabilityTheory.variance W P)⁻¹ *
        ∫ ω, -(W ω * (Iic w).indicator 1 (W ω)) ∂P by rw [hleft, integral_neg]; ring]
    refine mul_nonneg (inv_nonneg.mpr hVar.le) (integral_nonneg fun ω ↦ ?_)
    by_cases hle : W ω ≤ w
    · rw [indicator_of_mem (show W ω ∈ Iic w from hle), Pi.one_apply, mul_one]
      exact neg_nonneg.mpr (hle.trans hw.le)
    · simp [show W ω ∉ Iic w from hle]

/-- Measurability of `zeroBiasDensity P W`, derived from monotonicity on `(-∞, 0]` and antitonicity
on `[0, ∞)` (`SteinIntro.tex:1481-1483`). -/
theorem measurable_zeroBiasDensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    Measurable (zeroBiasDensity P W) := by
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW_aem : AEMeasurable W P := hW2.aemeasurable
  have hind_int : ∀ s : Set ℝ, MeasurableSet s →
      Integrable (fun ω ↦ W ω * s.indicator 1 (W ω)) P := fun s hs ↦ by
    refine hW_int.norm.mono'
      (hW2.aestronglyMeasurable.mul
        ((measurable_one.indicator hs).comp_aemeasurable hW_aem).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ ?_)
    by_cases hω : W ω ∈ s <;> simp [hω]
  let g_pos : ℝ → ℝ := fun w ↦ zeroBiasDensity P W (max 0 w)
  let g_neg : ℝ → ℝ := fun w ↦ zeroBiasDensity P W (min 0 w)
  have h_anti : Antitone g_pos := fun u v huv ↦ by
    dsimp [g_pos, zeroBiasDensity]
    have hmax : max 0 u ≤ max 0 v := max_le_max_left 0 huv
    refine mul_le_mul_of_nonneg_left
      (integral_mono (hind_int _ measurableSet_Ioi) (hind_int _ measurableSet_Ioi) fun ω ↦ ?_)
      (inv_nonneg.mpr hVar.le)
    by_cases h2 : max 0 v < W ω
    · have h1 : max 0 u < W ω := lt_of_le_of_lt hmax h2
      have hm2 : W ω ∈ Ioi (max 0 v) := h2
      have hm1 : W ω ∈ Ioi (max 0 u) := h1
      simp [hm1, hm2]
    · have hn2 : W ω ∉ Ioi (max 0 v) := h2
      rw [indicator_of_notMem hn2, mul_zero]
      by_cases h1 : max 0 u < W ω
      · have hm1 : W ω ∈ Ioi (max 0 u) := h1
        rw [indicator_of_mem hm1, Pi.one_apply, mul_one]
        exact (le_max_left 0 u).trans h1.le
      · have hn1 : W ω ∉ Ioi (max 0 u) := h1
        simp [hn1]
  have h_mono : Monotone g_neg := fun u v huv ↦ by
    dsimp [g_neg]
    have hlu : zeroBiasDensity P W (min 0 u) =
        (ProbabilityTheory.variance W P)⁻¹ *
          ∫ ω, -(W ω * (Iic (min 0 u)).indicator 1 (W ω)) ∂P := by
      rw [(zeroBiasDensity_left_tail_and_nonneg P hW2 hMean hVar (min 0 u)).1, integral_neg]
      ring
    have hlv : zeroBiasDensity P W (min 0 v) =
        (ProbabilityTheory.variance W P)⁻¹ *
          ∫ ω, -(W ω * (Iic (min 0 v)).indicator 1 (W ω)) ∂P := by
      rw [(zeroBiasDensity_left_tail_and_nonneg P hW2 hMean hVar (min 0 v)).1, integral_neg]
      ring
    rw [hlu, hlv]
    have hmin : min 0 u ≤ min 0 v := min_le_min_left 0 huv
    refine mul_le_mul_of_nonneg_left
      (integral_mono (hind_int _ measurableSet_Iic).neg (hind_int _ measurableSet_Iic).neg
        fun ω ↦ ?_)
      (inv_nonneg.mpr hVar.le)
    by_cases h1 : W ω ≤ min 0 u
    · have h2 : W ω ≤ min 0 v := h1.trans hmin
      have hm1 : W ω ∈ Iic (min 0 u) := h1
      have hm2 : W ω ∈ Iic (min 0 v) := h2
      simp [hm1, hm2]
    · have hn1 : W ω ∉ Iic (min 0 u) := h1
      rw [indicator_of_notMem hn1, mul_zero, neg_zero]
      by_cases h2 : W ω ≤ min 0 v
      · have hm2 : W ω ∈ Iic (min 0 v) := h2
        rw [indicator_of_mem hm2, Pi.one_apply, mul_one]
        exact neg_nonneg.mpr (h2.trans (min_le_left 0 v))
      · have hn2 : W ω ∉ Iic (min 0 v) := h2
        simp [hn2]
  have heq : zeroBiasDensity P W = fun w ↦ if 0 ≤ w then g_pos w else g_neg w := by
    ext w
    by_cases hw : 0 ≤ w
    · simp [g_pos, hw]
    · simp [g_neg, hw, le_of_not_ge hw]
  rw [heq]
  exact Measurable.ite measurableSet_Ici h_anti.measurable h_mono.measurable

private lemma zeroBiasDensity_eq_map
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW2 : MemLp W 2 P) (w : ℝ) :
    zeroBiasDensity P W w =
      (ProbabilityTheory.variance W P)⁻¹ * ∫ x in Ioi w, x ∂(P.map W) := by
  have hW_aem : AEMeasurable W P := hW2.aemeasurable
  unfold zeroBiasDensity
  congr 1
  have hmeas : Measurable (fun x : ℝ ↦ x * (Ioi w).indicator 1 x) :=
    measurable_id.mul (measurable_one.indicator measurableSet_Ioi)
  rw [← integral_map hW_aem hmeas.aestronglyMeasurable, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ Ioi w <;> simp [hx]

private lemma zeroBiasDensity_left_eq_map
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P) (w : ℝ) :
    zeroBiasDensity P W w =
      (ProbabilityTheory.variance W P)⁻¹ * ∫ x in Iic w, (-x) ∂(P.map W) := by
  have hW_aem : AEMeasurable W P := hW2.aemeasurable
  have hleft : zeroBiasDensity P W w =
      (ProbabilityTheory.variance W P)⁻¹ *
        ∫ ω, -(W ω * (Iic w).indicator 1 (W ω)) ∂P := by
    rw [(zeroBiasDensity_left_tail_and_nonneg P hW2 hMean hVar w).1, integral_neg]
    ring
  rw [hleft]
  congr 1
  have hmeas : Measurable (fun x : ℝ ↦ -(x * (Iic w).indicator 1 x)) :=
    (measurable_id.mul (measurable_one.indicator measurableSet_Iic)).neg
  rw [← integral_map hW_aem hmeas.aestronglyMeasurable, ← integral_indicator measurableSet_Iic]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ Iic w <;> simp [hx]

private lemma isProbabilityMeasure_zeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    IsProbabilityMeasure
      (volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))) := by
  set σ2 : ℝ := ProbabilityTheory.variance W P
  set μ : Measure ℝ := P.map W
  have hW_aem : AEMeasurable W P := hW2.aemeasurable
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (P.map W))
  have hid_L2 : MemLp (fun x : ℝ ↦ x) 2 μ :=
    (memLp_map_measure_iff aestronglyMeasurable_id hW_aem).mpr hW2
  have hid_int : Integrable (fun x : ℝ ↦ x) μ := hid_L2.integrable one_le_two
  have hneg_int : Integrable (fun x : ℝ ↦ -x) μ := hid_int.neg
  have hsq_int : Integrable (fun x : ℝ ↦ x ^ 2) μ := hid_L2.integrable_sq
  have hvar_eq : ∫ x, x ^ 2 ∂μ = σ2 := by
    have hv := ProbabilityTheory.variance_of_integral_eq_zero hW_aem hMean
    rw [← integral_map hW_aem (continuous_pow 2).measurable.aestronglyMeasurable] at hv
    exact hv.symm
  let S_pos : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1}
  let H_pos : ℝ × ℝ → ℝ≥0∞ := S_pos.indicator fun p ↦ ENNReal.ofReal p.1
  have hS_pos_meas : MeasurableSet S_pos :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hH_pos_meas : Measurable H_pos :=
    (ENNReal.measurable_ofReal.comp measurable_fst).indicator hS_pos_meas
  have h_pos_fub :
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (∫ x in Ioi t, x ∂μ) ∂volume =
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ 2) ∂μ := by
    calc
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (∫ x in Ioi t, x ∂μ) ∂volume
        = ∫⁻ t, (Ioi (0 : ℝ)).indicator (fun t ↦ ∫⁻ x, H_pos (x, t) ∂μ) t ∂volume := by
          rw [lintegral_indicator measurableSet_Ioi]
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
          have hnn : 0 ≤ᵐ[μ.restrict (Ioi t)] fun x : ℝ ↦ x := by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact (ht.trans hx).le
          rw [ofReal_integral_eq_lintegral_ofReal hid_int.integrableOn hnn,
            ← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun x ↦ ?_
          by_cases hxt : t < x
          · simp [H_pos, (show x ∈ Ioi t from hxt), (show (x, t) ∈ S_pos from ⟨ht, hxt⟩)]
          · simp [H_pos, (show x ∉ Ioi t from hxt), (show (x, t) ∉ S_pos from fun h ↦ hxt h.2)]
      _ = ∫⁻ t, ∫⁻ x, H_pos (x, t) ∂μ ∂volume := by
          refine lintegral_congr fun t ↦ ?_
          by_cases ht : 0 < t
          · simp [show t ∈ Ioi (0 : ℝ) from ht]
          · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
            simp [show (fun x ↦ H_pos (x, t)) = fun _ ↦ 0 by ext x; simp [H_pos, S_pos, ht]]
      _ = ∫⁻ x, ∫⁻ t, H_pos (x, t) ∂volume ∂μ :=
          lintegral_lintegral_swap (f := fun t x ↦ H_pos (x, t))
            (hH_pos_meas.comp measurable_swap).aemeasurable
      _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ 2) ∂μ := by
          rw [← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : 0 < x
          · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
            have hslice : (fun t ↦ H_pos (x, t)) =
                (Ioo 0 x).indicator (fun _ ↦ ENNReal.ofReal x) := by
              ext t; by_cases ht : 0 < t ∧ t < x <;> simp [H_pos, S_pos, ht]
            rw [hslice, lintegral_indicator measurableSet_Ioo, setLIntegral_const,
              Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul hx.le, sq]
          · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
            have h0 : (fun t ↦ H_pos (x, t)) = fun _ ↦ 0 := by
              ext t; simp [H_pos, S_pos, (show ¬(0 < t ∧ t < x) from fun h ↦ hx (h.1.trans h.2))]
            simp [h0]
  let S_neg : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ 0}
  let H_neg : ℝ × ℝ → ℝ≥0∞ := S_neg.indicator fun p ↦ ENNReal.ofReal (-p.1)
  have hS_neg_meas : MeasurableSet S_neg :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hH_neg_meas : Measurable H_neg :=
    (ENNReal.measurable_ofReal.comp measurable_fst.neg).indicator hS_neg_meas
  have h_neg_fub :
      ∫⁻ t in Iic (0 : ℝ), ENNReal.ofReal (∫ x in Iic t, (-x) ∂μ) ∂volume =
        ∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (x ^ 2) ∂μ := by
    calc
      ∫⁻ t in Iic (0 : ℝ), ENNReal.ofReal (∫ x in Iic t, (-x) ∂μ) ∂volume
        = ∫⁻ t, (Iic (0 : ℝ)).indicator (fun t ↦ ∫⁻ x, H_neg (x, t) ∂μ) t ∂volume := by
          rw [lintegral_indicator measurableSet_Iic]
          refine setLIntegral_congr_fun measurableSet_Iic fun t ht ↦ ?_
          have hnn : 0 ≤ᵐ[μ.restrict (Iic t)] fun x : ℝ ↦ -x := by
            filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
            exact neg_nonneg.mpr (hx.trans ht)
          rw [ofReal_integral_eq_lintegral_ofReal hneg_int.integrableOn hnn,
            ← lintegral_indicator measurableSet_Iic]
          refine lintegral_congr fun x ↦ ?_
          by_cases hxt : x ≤ t
          · simp [H_neg, (show x ∈ Iic t from hxt), (show (x, t) ∈ S_neg from ⟨hxt, ht⟩)]
          · simp [H_neg, (show x ∉ Iic t from hxt), (show (x, t) ∉ S_neg from fun h ↦ hxt h.1)]
      _ = ∫⁻ t, ∫⁻ x, H_neg (x, t) ∂μ ∂volume := by
          refine lintegral_congr fun t ↦ ?_
          by_cases ht : t ≤ 0
          · simp [show t ∈ Iic (0 : ℝ) from ht]
          · rw [indicator_of_notMem (show t ∉ Iic (0 : ℝ) from ht)]
            simp [show (fun x ↦ H_neg (x, t)) = fun _ ↦ 0 by ext x; simp [H_neg, S_neg, ht]]
      _ = ∫⁻ x, ∫⁻ t, H_neg (x, t) ∂volume ∂μ :=
          lintegral_lintegral_swap (f := fun t x ↦ H_neg (x, t))
            (hH_neg_meas.comp measurable_swap).aemeasurable
      _ = ∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (x ^ 2) ∂μ := by
          rw [← lintegral_indicator measurableSet_Iic]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ≤ 0
          · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
            have hslice : (fun t ↦ H_neg (x, t)) =
                (Icc x 0).indicator (fun _ ↦ ENNReal.ofReal (-x)) := by
              ext t; by_cases ht : x ≤ t ∧ t ≤ 0 <;> simp [H_neg, S_neg, ht]
            rw [hslice, lintegral_indicator measurableSet_Icc, setLIntegral_const,
              Real.volume_Icc, zero_sub, ← ENNReal.ofReal_mul (neg_nonneg.mpr hx)]
            congr 1; ring
          · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx)]
            have h0 : (fun t ↦ H_neg (x, t)) = fun _ ↦ 0 := by
              ext t; simp [H_neg, S_neg, (show ¬(x ≤ t ∧ t ≤ 0) from fun h ↦ hx (h.1.trans h.2))]
            simp [h0]
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    lintegral_union measurableSet_Ioi (Iic_disjoint_Ioi le_rfl)]
  have hm_neg : Measurable (fun w ↦ ENNReal.ofReal (∫ x in Iic w, (-x) ∂μ)) := by
    have heq : (fun w ↦ ENNReal.ofReal (∫ x in Iic w, (-x) ∂μ)) =
        fun w ↦ ENNReal.ofReal (σ2 * zeroBiasDensity P W w) := by
      ext w; rw [zeroBiasDensity_left_eq_map P hW2 hMean hVar w, ← mul_assoc,
        mul_inv_cancel₀ hVar.ne', one_mul]
    rw [heq]
    exact ENNReal.measurable_ofReal.comp
      ((measurable_zeroBiasDensity P hW2 hMean hVar).const_mul σ2)
  have hm_pos : Measurable (fun w ↦ ENNReal.ofReal (∫ x in Ioi w, x ∂μ)) := by
    have heq : (fun w ↦ ENNReal.ofReal (∫ x in Ioi w, x ∂μ)) =
        fun w ↦ ENNReal.ofReal (σ2 * zeroBiasDensity P W w) := by
      ext w; rw [zeroBiasDensity_eq_map P hW2 w, ← mul_assoc, mul_inv_cancel₀ hVar.ne', one_mul]
    rw [heq]
    exact ENNReal.measurable_ofReal.comp
      ((measurable_zeroBiasDensity P hW2 hMean hVar).const_mul σ2)
  have h1 : ∫⁻ w in Iic (0 : ℝ), ENNReal.ofReal (zeroBiasDensity P W w) ∂volume =
      ENNReal.ofReal σ2⁻¹ * ∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (x ^ 2) ∂μ := by
    have hcongr : ∫⁻ w in Iic (0 : ℝ), ENNReal.ofReal (zeroBiasDensity P W w) ∂volume =
        ∫⁻ w in Iic (0 : ℝ),
          ENNReal.ofReal σ2⁻¹ * ENNReal.ofReal (∫ x in Iic w, (-x) ∂μ) ∂volume :=
      setLIntegral_congr_fun measurableSet_Iic fun w _ ↦ by
        rw [zeroBiasDensity_left_eq_map P hW2 hMean hVar w,
          ENNReal.ofReal_mul (inv_nonneg.mpr hVar.le)]
    rw [hcongr, lintegral_const_mul _ hm_neg, h_neg_fub]
  have h2 : ∫⁻ w in Ioi (0 : ℝ), ENNReal.ofReal (zeroBiasDensity P W w) ∂volume =
      ENNReal.ofReal σ2⁻¹ * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ 2) ∂μ := by
    have hcongr : ∫⁻ w in Ioi (0 : ℝ), ENNReal.ofReal (zeroBiasDensity P W w) ∂volume =
        ∫⁻ w in Ioi (0 : ℝ),
          ENNReal.ofReal σ2⁻¹ * ENNReal.ofReal (∫ x in Ioi w, x ∂μ) ∂volume :=
      setLIntegral_congr_fun measurableSet_Ioi fun w _ ↦ by
        rw [zeroBiasDensity_eq_map P hW2 w, ENNReal.ofReal_mul (inv_nonneg.mpr hVar.le)]
    rw [hcongr, lintegral_const_mul _ hm_pos, h_pos_fub]
  rw [h1, h2, ← mul_add, ← lintegral_union measurableSet_Ioi (Iic_disjoint_Ioi le_rfl),
    Iic_union_Ioi, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hsq_int (ae_of_all _ sq_nonneg), hvar_eq,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hVar.le), inv_mul_cancel₀ hVar.ne', ENNReal.ofReal_one]

private lemma isZeroBias_zeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    let ν : Measure ℝ := volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))
    IsZeroBias P W ν id := by
  intro ν
  set σ2 : ℝ := ProbabilityTheory.variance W P
  set pz : ℝ → ℝ := zeroBiasDensity P W
  set μ : Measure ℝ := P.map W
  have hW_aem : AEMeasurable W P := hW2.aemeasurable
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (P.map W))
  have hid_int : Integrable (fun x : ℝ ↦ x) μ :=
    (integrable_map_measure aestronglyMeasurable_id hW_aem).mpr (hW2.integrable one_le_two)
  have hpz_meas : Measurable pz := measurable_zeroBiasDensity P hW2 hMean hVar
  have hpz_nn : ∀ w : ℝ, 0 ≤ pz w :=
    fun w ↦ (zeroBiasDensity_left_tail_and_nonneg P hW2 hMean hVar w).2
  refine ⟨hW2, hMean, aemeasurable_id, ?_⟩
  intro f hf hWf_int hf'_ν
  have hf_cont : Continuous f := continuous_of_locallyAC hf
  have hd_meas : Measurable (fun w ↦ ENNReal.ofReal (pz w)) :=
    ENNReal.measurable_ofReal.comp hpz_meas
  have hd_lt_top : ∀ᵐ w ∂volume, ENNReal.ofReal (pz w) < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hf'_vol : Integrable (fun t ↦ deriv f t * pz t) volume := by
    change Integrable (deriv f) (volume.withDensity (fun w ↦ ENNReal.ofReal (pz w))) at hf'_ν
    have hiff := (integrable_withDensity_iff_integrable_smul' hd_meas hd_lt_top).mp hf'_ν
    refine hiff.congr (ae_of_all _ fun t ↦ ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hpz_nn t), smul_eq_mul, mul_comm]
  have hν_int_eq : ∫ t, deriv f t ∂ν = ∫ t, deriv f t * pz t ∂volume := by
    change ∫ t, deriv f t ∂(volume.withDensity (fun w ↦ ENNReal.ofReal (pz w))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hd_meas hd_lt_top]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hpz_nn t), smul_eq_mul, mul_comm]
  let S_pos : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1}
  let K_pos : ℝ × ℝ → ℝ := S_pos.indicator fun p ↦ deriv f p.2 * p.1
  have hS_pos_meas : MeasurableSet S_pos :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hK_pos_meas : Measurable K_pos :=
    (((measurable_deriv f).comp measurable_snd).mul measurable_fst).indicator hS_pos_meas
  have hK_pos_int : Integrable K_pos (μ.prod volume) := by
    rw [integrable_prod_iff' hK_pos_meas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
    · by_cases ht : 0 < t
      · have h_ind : (fun x ↦ K_pos (x, t)) = (Ioi t).indicator (fun x ↦ deriv f t * x) := by
          ext x; by_cases hxt : t < x <;> simp [K_pos, S_pos, ht, hxt]
        rw [h_ind]
        exact (hid_int.const_mul (deriv f t)).indicator measurableSet_Ioi
      · have h0 : (fun x ↦ K_pos (x, t)) = 0 := by ext x; simp [K_pos, S_pos, ht]
        rw [h0]; exact integrable_zero _ _ _
    · have hnorm : (fun t ↦ ∫ x, ‖K_pos (x, t)‖ ∂μ) =
          (Ioi (0 : ℝ)).indicator (fun t ↦ σ2 * (|deriv f t| * pz t)) := by
        ext t
        by_cases ht : 0 < t
        · have hm : t ∈ Ioi (0 : ℝ) := ht
          have hslice : (fun x ↦ ‖K_pos (x, t)‖) =
              (Ioi t).indicator (fun x ↦ |deriv f t| * x) := by
            ext x
            by_cases hxt : t < x
            · have hx0 : 0 ≤ x := (ht.trans hxt).le
              simp [K_pos, S_pos, ht, hxt, abs_of_nonneg hx0]
            · simp [K_pos, S_pos, ht, hxt]
          rw [hslice, integral_indicator measurableSet_Ioi, integral_const_mul,
            indicator_of_mem hm]
          have hpzt := zeroBiasDensity_eq_map P hW2 t
          change pz t = σ2⁻¹ * ∫ x in Ioi t, x ∂μ at hpzt
          have hmul : ∫ x in Ioi t, x ∂μ = σ2 * pz t := by
            rw [hpzt, ← mul_assoc, mul_inv_cancel₀ hVar.ne', one_mul]
          rw [hmul]; ring
        · have hn : t ∉ Ioi (0 : ℝ) := ht
          have h0 : (fun x ↦ ‖K_pos (x, t)‖) = 0 := by ext x; simp [K_pos, S_pos, ht]
          rw [h0, Pi.zero_def, integral_zero, indicator_of_notMem hn]
      rw [hnorm]
      have habs : (fun t ↦ σ2 * (|deriv f t| * pz t)) =
          fun t ↦ σ2 * ‖deriv f t * pz t‖ := by
        ext t; simp [abs_of_nonneg (hpz_nn t)]
      rw [habs]
      exact (hf'_vol.norm.const_mul σ2).indicator measurableSet_Ioi
  have h_pos_eq :
      ∫ x in Ioi (0 : ℝ), x * (f x - f 0) ∂μ =
        σ2 * ∫ t in Ioi (0 : ℝ), deriv f t * pz t ∂volume := by
    have h_left : (fun x ↦ ∫ t, K_pos (x, t) ∂volume) =
        (Ioi (0 : ℝ)).indicator (fun x ↦ x * (f x - f 0)) := by
      ext x
      by_cases hx : 0 < x
      · have hm : x ∈ Ioi (0 : ℝ) := hx
        have hslice : (fun t ↦ K_pos (x, t)) = (Ioo 0 x).indicator (fun t ↦ deriv f t * x) := by
          ext t; by_cases ht : 0 < t ∧ t < x <;> simp [K_pos, S_pos, ht]
        rw [hslice, integral_indicator measurableSet_Ioo, integral_mul_const,
          setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hx.le,
          (hf 0 x).integral_deriv_eq_sub, indicator_of_mem hm, mul_comm]
      · have hn : x ∉ Ioi (0 : ℝ) := hx
        have h0 : (fun t ↦ K_pos (x, t)) = 0 := by
          ext t
          have hnot : ¬ (0 < t ∧ t < x) := fun h ↦ hx (h.1.trans h.2)
          simp [K_pos, S_pos, hnot]
        rw [h0, Pi.zero_def, integral_zero, indicator_of_notMem hn]
    have h_right : (fun t ↦ ∫ x, K_pos (x, t) ∂μ) =
        (Ioi (0 : ℝ)).indicator (fun t ↦ σ2 * (deriv f t * pz t)) := by
      ext t
      by_cases ht : 0 < t
      · have hm : t ∈ Ioi (0 : ℝ) := ht
        have hslice : (fun x ↦ K_pos (x, t)) = (Ioi t).indicator (fun x ↦ deriv f t * x) := by
          ext x; by_cases hxt : t < x <;> simp [K_pos, S_pos, ht, hxt]
        rw [hslice, integral_indicator measurableSet_Ioi, integral_const_mul, indicator_of_mem hm]
        have hpzt := zeroBiasDensity_eq_map P hW2 t
        change pz t = σ2⁻¹ * ∫ x in Ioi t, x ∂μ at hpzt
        have hmul : ∫ x in Ioi t, x ∂μ = σ2 * pz t := by
          rw [hpzt, ← mul_assoc, mul_inv_cancel₀ hVar.ne', one_mul]
        rw [hmul]; ring
      · have hn : t ∉ Ioi (0 : ℝ) := ht
        have h0 : (fun x ↦ K_pos (x, t)) = 0 := by ext x; simp [K_pos, S_pos, ht]
        rw [h0, Pi.zero_def, integral_zero, indicator_of_notMem hn]
    have hfub := (integral_prod K_pos hK_pos_int).symm.trans (integral_prod_symm K_pos hK_pos_int)
    rw [h_left, integral_indicator measurableSet_Ioi, h_right,
      integral_indicator measurableSet_Ioi, integral_const_mul] at hfub
    exact hfub
  let S_neg : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ 0}
  let K_neg : ℝ × ℝ → ℝ := S_neg.indicator fun p ↦ deriv f p.2 * (-p.1)
  have hS_neg_meas : MeasurableSet S_neg :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hK_neg_meas : Measurable K_neg :=
    (((measurable_deriv f).comp measurable_snd).mul measurable_fst.neg).indicator hS_neg_meas
  have hK_neg_int : Integrable K_neg (μ.prod volume) := by
    rw [integrable_prod_iff' hK_neg_meas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
    · by_cases ht : t ≤ 0
      · have h_ind : (fun x ↦ K_neg (x, t)) = (Iic t).indicator (fun x ↦ deriv f t * (-x)) := by
          ext x; by_cases hxt : x ≤ t <;> simp [K_neg, S_neg, ht, hxt]
        rw [h_ind]
        exact (hid_int.neg.const_mul (deriv f t)).indicator measurableSet_Iic
      · have h0 : (fun x ↦ K_neg (x, t)) = 0 := by ext x; simp [K_neg, S_neg, ht]
        rw [h0]; exact integrable_zero _ _ _
    · have hnorm : (fun t ↦ ∫ x, ‖K_neg (x, t)‖ ∂μ) =
          (Iic (0 : ℝ)).indicator (fun t ↦ σ2 * (|deriv f t| * pz t)) := by
        ext t
        by_cases ht : t ≤ 0
        · have hm : t ∈ Iic (0 : ℝ) := ht
          have hslice : (fun x ↦ ‖K_neg (x, t)‖) =
              (Iic t).indicator (fun x ↦ |deriv f t| * (-x)) := by
            ext x
            by_cases hxt : x ≤ t
            · simp [K_neg, S_neg, ht, hxt, abs_of_nonpos (hxt.trans ht), mul_neg]
            · simp [K_neg, S_neg, ht, hxt]
          rw [hslice, integral_indicator measurableSet_Iic, integral_const_mul,
            indicator_of_mem hm]
          have hpzt := zeroBiasDensity_left_eq_map P hW2 hMean hVar t
          change pz t = σ2⁻¹ * ∫ x in Iic t, (-x) ∂μ at hpzt
          have hmul : ∫ x in Iic t, (-x) ∂μ = σ2 * pz t := by
            rw [hpzt, ← mul_assoc, mul_inv_cancel₀ hVar.ne', one_mul]
          rw [hmul]; ring
        · have hn : t ∉ Iic (0 : ℝ) := ht
          have h0 : (fun x ↦ ‖K_neg (x, t)‖) = 0 := by ext x; simp [K_neg, S_neg, ht]
          rw [h0, Pi.zero_def, integral_zero, indicator_of_notMem hn]
      rw [hnorm]
      have habs : (fun t ↦ σ2 * (|deriv f t| * pz t)) =
          fun t ↦ σ2 * ‖deriv f t * pz t‖ := by
        ext t; simp [abs_of_nonneg (hpz_nn t)]
      rw [habs]
      exact (hf'_vol.norm.const_mul σ2).indicator measurableSet_Iic
  have h_neg_eq :
      ∫ x in Iic (0 : ℝ), x * (f x - f 0) ∂μ =
        σ2 * ∫ t in Iic (0 : ℝ), deriv f t * pz t ∂volume := by
    have h_left : (fun x ↦ ∫ t, K_neg (x, t) ∂volume) =
        (Iic (0 : ℝ)).indicator (fun x ↦ x * (f x - f 0)) := by
      ext x
      by_cases hx : x ≤ 0
      · have hm : x ∈ Iic (0 : ℝ) := hx
        have hslice : (fun t ↦ K_neg (x, t)) =
            (Icc x 0).indicator (fun t ↦ deriv f t * (-x)) := by
          ext t; by_cases ht : x ≤ t ∧ t ≤ 0 <;> simp [K_neg, S_neg, ht]
        rw [hslice, integral_indicator measurableSet_Icc, integral_mul_const,
          ← setIntegral_congr_set Ioc_ae_eq_Icc, ← intervalIntegral.integral_of_le hx,
          (hf x 0).integral_deriv_eq_sub, indicator_of_mem hm]
        ring
      · have hn : x ∉ Iic (0 : ℝ) := hx
        have h0 : (fun t ↦ K_neg (x, t)) = 0 := by
          ext t
          have hnot : ¬ (x ≤ t ∧ t ≤ 0) := fun h ↦ hx (h.1.trans h.2)
          simp [K_neg, S_neg, hnot]
        rw [h0, Pi.zero_def, integral_zero, indicator_of_notMem hn]
    have h_right : (fun t ↦ ∫ x, K_neg (x, t) ∂μ) =
        (Iic (0 : ℝ)).indicator (fun t ↦ σ2 * (deriv f t * pz t)) := by
      ext t
      by_cases ht : t ≤ 0
      · have hm : t ∈ Iic (0 : ℝ) := ht
        have hslice : (fun x ↦ K_neg (x, t)) = (Iic t).indicator (fun x ↦ deriv f t * (-x)) := by
          ext x; by_cases hxt : x ≤ t <;> simp [K_neg, S_neg, ht, hxt]
        rw [hslice, integral_indicator measurableSet_Iic, integral_const_mul, indicator_of_mem hm]
        have hpzt := zeroBiasDensity_left_eq_map P hW2 hMean hVar t
        change pz t = σ2⁻¹ * ∫ x in Iic t, (-x) ∂μ at hpzt
        have hmul : ∫ x in Iic t, (-x) ∂μ = σ2 * pz t := by
          rw [hpzt, ← mul_assoc, mul_inv_cancel₀ hVar.ne', one_mul]
        rw [hmul]; ring
      · have hn : t ∉ Iic (0 : ℝ) := ht
        have h0 : (fun x ↦ K_neg (x, t)) = 0 := by ext x; simp [K_neg, S_neg, ht]
        rw [h0, Pi.zero_def, integral_zero, indicator_of_notMem hn]
    have hfub := (integral_prod K_neg hK_neg_int).symm.trans (integral_prod_symm K_neg hK_neg_int)
    rw [h_left, integral_indicator measurableSet_Iic, h_right,
      integral_indicator measurableSet_Iic, integral_const_mul] at hfub
    exact hfub
  have hWf_μ : Integrable (fun x : ℝ ↦ x * f x) μ :=
    (integrable_map_measure (measurable_id.mul hf_cont.measurable).aestronglyMeasurable
      hW_aem).mpr hWf_int
  have hsub_μ : Integrable (fun x : ℝ ↦ x * (f x - f 0)) μ := by
    have heq : (fun x : ℝ ↦ x * (f x - f 0)) = fun x ↦ x * f x - f 0 * x := by ext x; ring
    rw [heq]
    exact hWf_μ.sub (hid_int.const_mul (f 0))
  have hmean_μ : ∫ x, x ∂μ = 0 := by
    dsimp [μ]; rw [integral_map hW_aem (f := fun x ↦ x) aestronglyMeasurable_id, hMean]
  have hfull_sub : ∫ x, x * (f x - f 0) ∂μ = σ2 * ∫ t, deriv f t * pz t ∂volume := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hsub_μ.integrableOn hsub_μ.integrableOn,
      h_neg_eq, h_pos_eq, ← mul_add,
      ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hf'_vol.integrableOn hf'_vol.integrableOn,
      Iic_union_Ioi, setIntegral_univ]
  have hdecomp : (fun x : ℝ ↦ x * f x) = fun x ↦ x * (f x - f 0) + f 0 * x := by ext x; ring
  calc
    ∫ ω, W ω * f (W ω) ∂P
      = ∫ x, x * f x ∂μ :=
        (integral_map hW_aem (measurable_id.mul hf_cont.measurable).aestronglyMeasurable).symm
    _ = (∫ x, x * (f x - f 0) ∂μ) + ∫ x, f 0 * x ∂μ := by
        rw [hdecomp, integral_add hsub_μ (hid_int.const_mul (f 0))]
    _ = σ2 * ∫ t, deriv f t * pz t ∂volume := by
        rw [hfull_sub, integral_const_mul, hmean_μ, mul_zero, add_zero]
    _ = σ2 * ∫ t, deriv f t ∂ν := by rw [hν_int_eq]

/-- Ramp approximation `zbRamp x n` to `(Iic x).indicator 1` used for CDF identification. -/
def zbRamp (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (1 - ((n : ℝ) + 1) * (t - x)))

lemma continuous_zbRamp (x : ℝ) (n : ℕ) : Continuous (zbRamp x n) := by
  unfold zbRamp; fun_prop

lemma abs_zbRamp_le_one (x : ℝ) (n : ℕ) (t : ℝ) : |zbRamp x n t| ≤ 1 := by
  rw [abs_of_nonneg (le_max_left 0 _)]
  exact max_le zero_le_one (min_le_left 1 _)

lemma tendsto_integral_zbRamp (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Tendsto (fun n ↦ ∫ t, zbRamp x n t ∂μ) atTop (𝓝 (cdf μ x)) := by
  have htend : ∀ t : ℝ, Tendsto (fun n ↦ zbRamp x n t) atTop (𝓝 ((Iic x).indicator 1 t)) := by
    intro t
    by_cases htx : t ≤ x
    · have hm : t ∈ Iic x := htx
      rw [indicator_of_mem hm]
      have heq : ∀ n : ℕ, zbRamp x n t = 1 := fun n ↦ by
        have hmul : ((n : ℝ) + 1) * (t - x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr htx)
        have h1 : 1 ≤ 1 - ((n : ℝ) + 1) * (t - x) := by linarith
        simp [zbRamp, min_eq_left h1]
      simp_rw [heq]; exact tendsto_const_nhds
    · have hn : t ∉ Iic x := htx
      rw [indicator_of_notMem hn]
      have hxt : 0 < t - x := sub_pos.mpr (lt_of_not_ge htx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.Ici_mem_atTop ⌈(t - x)⁻¹⌉₊] with n hn_ge
      have hn1 : (t - x)⁻¹ ≤ (n : ℝ) + 1 := by
        linarith [(Nat.le_ceil (t - x)⁻¹).trans (Nat.cast_le.mpr hn_ge)]
      have hmul : 1 ≤ ((n : ℝ) + 1) * (t - x) := by
        have := mul_le_mul_of_nonneg_right hn1 hxt.le
        rwa [inv_mul_cancel₀ hxt.ne'] at this
      exact (max_eq_left ((min_le_right 1 _).trans (by linarith))).symm
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ (1 : ℝ))
    (fun n ↦ (continuous_zbRamp x n).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n ↦ ae_of_all μ fun t ↦ by rw [Real.norm_eq_abs]; exact abs_zbRamp_le_one x n t)
    (ae_of_all μ htend)
  have hind : ∫ t, (Iic x).indicator (1 : ℝ → ℝ) t ∂μ = cdf μ x := by
    rw [integral_indicator measurableSet_Iic, Pi.one_def, setIntegral_const, smul_eq_mul,
      mul_one, ← cdf_eq_real]
  rwa [hind] at hlim

/-- Sublinear-$C^1$ sufficient criterion for `IsZeroBias` when $\operatorname{Var}(W) > 0$:
if `Wz` satisfies $\mathbb{E}[W F(W)] = \operatorname{Var}(W)\,\mathbb{E}[F'(W^z)]$ for every $C^1$
function $F : \mathbb{R} \to \mathbb{R}$ with $|F(w)| \le |w|$ and bounded derivative, then the law
of `Wz` equals the canonical zero-bias law of `W` and `IsZeroBias P W P' Wz` holds for all locally
absolutely continuous test functions (`SteinIntro.tex:1512-1514`). -/
theorem isZeroBias_and_map_eq_of_c1_sublinear
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Wz : Ω' → ℝ}
    (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P)
    (hWz_meas : AEMeasurable Wz P')
    (hC1 : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → (∀ w : ℝ, |F w| ≤ |w|) →
      (∃ B : ℝ, ∀ w : ℝ, |deriv F w| ≤ B) →
      ∫ ω, W ω * F (W ω) ∂P =
        ProbabilityTheory.variance W P * ∫ ω', deriv F (Wz ω') ∂P') :
    P'.map Wz = volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w)) ∧
      IsZeroBias P W P' Wz := by
  set ν : Measure ℝ := volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))
  have : IsProbabilityMeasure ν := isProbabilityMeasure_zeroBiasLaw P hW2 hMean hVar
  have hZB_ν : IsZeroBias P W ν id := isZeroBias_zeroBiasLaw P hW2 hMean hVar
  have hmap_eq : P'.map Wz = ν := by
    refine Measure.eq_of_cdf (P'.map Wz) ν ?_
    ext x
    have heq_n : ∀ n : ℕ, ∫ t, zbRamp x n t ∂(P'.map Wz) = ∫ t, zbRamp x n t ∂ν := fun n ↦ by
      let g : ℝ → ℝ := zbRamp x n
      have hg_cont : Continuous g := continuous_zbRamp x n
      let F : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t, g u
      have hF_deriv : ∀ t : ℝ, HasDerivAt F (g t) t := fun t ↦
        intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 t)
          hg_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hg_cont.continuousAt
      have hderiv_eq : deriv F = g := funext fun t ↦ (hF_deriv t).deriv
      have hF_cd : ContDiff ℝ 1 F :=
        contDiff_one_iff_deriv.mpr ⟨fun t ↦ (hF_deriv t).differentiableAt, hderiv_eq ▸ hg_cont⟩
      have hF_sub : ∀ w : ℝ, |F w| ≤ |w| := fun w ↦ by
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := 0) (b := w) (C := 1) (f := g) fun u _ ↦ by
            rw [Real.norm_eq_abs]; exact abs_zbRamp_le_one x n u
        simpa [F, Real.norm_eq_abs] using hnorm
      have hF_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b := fun a b ↦
        hF_cd.contDiffOn.absolutelyContinuousOnInterval
      have hWF_int : Integrable (fun ω ↦ W ω * F (W ω)) P := by
        refine hW2.integrable_sq.mono'
          (hW2.aestronglyMeasurable.mul (hF_cd.continuous.measurable.comp_aemeasurable
            hW2.aemeasurable).aestronglyMeasurable)
          (ae_of_all _ fun ω ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, ← sq_abs, sq]
        exact mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (W ω))
      have hg_ν_int : Integrable (deriv F) ν := by
        rw [hderiv_eq]
        exact Integrable.of_bound hg_cont.aestronglyMeasurable 1
          (ae_of_all _ fun t ↦ by rw [Real.norm_eq_abs]; exact abs_zbRamp_le_one x n t)
      have h1 := hC1 F hF_cd hF_sub ⟨1, fun w ↦ by rw [hderiv_eq]; exact abs_zbRamp_le_one x n w⟩
      have h2 := hZB_ν.2.2.2 F hF_ac hWF_int hg_ν_int
      have h3 : ∫ ω', deriv F (Wz ω') ∂P' = ∫ t, deriv F t ∂ν :=
        mul_left_cancel₀ hVar.ne' (h1.symm.trans h2)
      rw [hderiv_eq] at h3
      rwa [integral_map hWz_meas hg_cont.aestronglyMeasurable]
    have hlim1 := tendsto_integral_zbRamp (P'.map Wz) x
    have hlim2 := tendsto_integral_zbRamp ν x
    simp_rw [heq_n] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2
  refine ⟨hmap_eq, ?_⟩
  have hid_Wz : IdentDistrib id Wz ν P' :=
    ⟨aemeasurable_id, hWz_meas, by rw [Measure.map_id, hmap_eq]⟩
  exact hZB_ν.congr_identDistrib (IdentDistrib.refl hW2.aemeasurable) hid_Wz

end DensityProperties

/-- **Proposition 3.19, corrected** (`\label{i81}`, `\label{i82}`, eqs. `(3.31)`–`(3.32)`
`\label{81}`–`\label{82}`, `SteinIntro.tex:1471-1485`; `ISSUE-3.10`, `ISSUE-3.19`, ruling `D9`):
for a mean-zero $L^2$ random variable $W$ with $\sigma^2 = \operatorname{Var}(W) > 0$,
`zeroBiasDensity P W` satisfies the left-tail formula and is nonnegative, uniquely determines the
law of every zero-bias variable $W^z$, and defines a probability measure whose identity map has
the zero-bias distribution with respect to $W$. -/
theorem zeroBias_law_characterization
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ}
    (hW2 : MemLp W 2 P) (hMean : ∫ ω, W ω ∂P = 0)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    (∀ w : ℝ,
        zeroBiasDensity P W w =
          -(ProbabilityTheory.variance W P)⁻¹ *
            ∫ ω, W ω * (Iic w).indicator 1 (W ω) ∂P ∧
          0 ≤ zeroBiasDensity P W w) ∧
      (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {Wz : Ω' → ℝ},
          IsZeroBias P W P' Wz →
          P'.map Wz =
            volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))) ∧
      (let ν : Measure ℝ :=
          volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))
       IsProbabilityMeasure ν ∧ IsZeroBias P W ν id) := by
  refine ⟨zeroBiasDensity_left_tail_and_nonneg P hW2 hMean hVar, ?_,
    isProbabilityMeasure_zeroBiasLaw P hW2 hMean hVar,
    isZeroBias_zeroBiasLaw P hW2 hMean hVar⟩
  intro P' _ Wz hZB
  refine (isZeroBias_and_map_eq_of_c1_sublinear P P' hW2 hMean hVar hZB.2.2.1 ?_).1
  intro F hF_cd hF_sub ⟨B, hB⟩
  have hF_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b := fun a b ↦
    hF_cd.contDiffOn.absolutelyContinuousOnInterval
  have hWF_int : Integrable (fun ω ↦ W ω * F (W ω)) P := by
    refine hW2.integrable_sq.mono'
      (hW2.aestronglyMeasurable.mul (hF_cd.continuous.measurable.comp_aemeasurable
        hW2.aemeasurable).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, ← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (W ω))
  have hF'_int : Integrable (fun ω' ↦ deriv F (Wz ω')) P' :=
    Integrable.of_bound
      ((measurable_deriv F).comp_aemeasurable hZB.2.2.1).aestronglyMeasurable B
      (ae_of_all _ fun ω' ↦ by rw [Real.norm_eq_abs]; exact hB (Wz ω'))
  exact hZB.2.2.2 F hF_ac hWF_int hF'_int

/-- Machine-checked counterexample to Proposition 3.19 at $\sigma^2 = 0$ (`ISSUE-3.19`,
`SteinIntro.tex:1471-1485`): when $W \equiv 0$, both $\delta_0$ and $\delta_1$ satisfy the
zero-bias relation with respect to $W$, refuting both uniqueness (`\label{i81}`) and Lebesgue
absolute continuity (`\label{i82}`). -/
theorem Prop3_19_sigma_zero_counterexample :
    ∃ (P : Measure ℝ) (_ : IsProbabilityMeasure P) (W Wz₁ Wz₂ : ℝ → ℝ),
      MemLp W 2 P ∧ ∫ ω, W ω ∂P = 0 ∧ ProbabilityTheory.variance W P = 0 ∧
      IsZeroBias P W P Wz₁ ∧ IsZeroBias P W P Wz₂ ∧
      P.map Wz₁ ≠ P.map Wz₂ ∧ ¬ (P.map Wz₁ ≪ volume) := by
  refine ⟨Measure.dirac 0, inferInstance, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 1,
    memLp_const 0, by simp, ProbabilityTheory.variance_zero (μ := Measure.dirac (0 : ℝ)),
    ?_, ?_, ?_, ?_⟩
  · refine ⟨memLp_const 0, by simp, aemeasurable_const, fun f _ _ _ ↦ ?_⟩
    rw [show (fun _ : ℝ ↦ (0 : ℝ)) = (0 : ℝ → ℝ) from rfl, ProbabilityTheory.variance_zero]; simp
  · refine ⟨memLp_const 0, by simp, aemeasurable_const, fun f _ _ _ ↦ ?_⟩
    rw [show (fun _ : ℝ ↦ (0 : ℝ)) = (0 : ℝ → ℝ) from rfl, ProbabilityTheory.variance_zero]; simp
  · intro heq
    have h0 : (Measure.map (fun _ : ℝ ↦ (0 : ℝ)) (Measure.dirac (0 : ℝ))) {(0 : ℝ)} = 1 := by simp
    have h1 : (Measure.map (fun _ : ℝ ↦ (1 : ℝ)) (Measure.dirac (0 : ℝ))) {(0 : ℝ)} = 0 := by simp
    rw [heq] at h0; exact one_ne_zero (h0.symm.trans h1)
  · intro hac
    have hmap : Measure.map (fun _ : ℝ ↦ (0 : ℝ)) (Measure.dirac (0 : ℝ)) = Measure.dirac 0 := by
      simp
    rw [hmap] at hac
    have h1 : (Measure.dirac (0 : ℝ)) {(0 : ℝ)} = 0 := hac Real.volume_singleton
    simp at h1

end SteinMethod
