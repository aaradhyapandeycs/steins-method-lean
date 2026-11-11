/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Kolmogorov
import Formalization.Defs.Metrics
import Formalization.Kolmogorov.Basic
import Formalization.Metrics.Basic
import Formalization.Normal.KolmogorovSolution
import Formalization.Normal.SolutionBounds

/-!
# Kolmogorov Stein Solution Bounds (`Formalization.Kolmogorov.SolutionBounds`)

Proves the general Kolmogorov Stein characterization, sharp and printed solution bounds, and smooth
test-class upper bound opening Section 3.6 of Nathan Ross, *"Fundamentals of Stein's method"*
(`Probability Surveys` 8, 2011; `arXiv:1109.1880v1`, `SteinIntro.tex:1666-1694`):

* `stdNormalCDF_mul_one_sub_div_pdf_le`: Pólya–Chu normal product inequality
  $\Phi(w)(1 - \Phi(w))/\phi(w) \le \sqrt{2\pi}/4$ ($4\Phi(w)(1 - \Phi(w)) \le e^{-w^2/2}$).
* `kolmogorovDist_map_stdNormal_eq_iSup_normalSteinOpLeft` (**Theorem 3.24**, `\label{thm91}`,
  eq. `(3.38)` `\label{91}`, `SteinIntro.tex:1666-1675`; `ISSUE-2.2`, `D4`).
* `lem3_25_corrected_bounds` (**Lemma 3.25**, `\label{lem91}`, `SteinIntro.tex:1677-1686`;
  `ISSUE-2.2`, `ISSUE-3.25`, `D4`), together with the sharp bounds
  `|normalSteinSolKolm x w| ≤ Real.sqrt (2 * Real.pi) / 4` and
  `|derivWithin (normalSteinSolKolm x) (Set.Iic w) w| ≤ 1`.
* `kolmogorovDist_map_stdNormal_le_iSup_normalSteinOp` (**Corollary 3.26**, `\label{cor91}`,
  `SteinIntro.tex:1688-1694`) via continuous ramp smoothing `kolmSmoothInd`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Pólya–Chu Normal Product Inequality -/

private noncomputable def polyaG (t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / 2) - 4 * stdNormalCDF t * (1 - stdNormalCDF t)

private noncomputable def polyaH (t : ℝ) : ℝ :=
  4 / Real.sqrt (2 * Real.pi) * (2 * stdNormalCDF t - 1) - t

private lemma hasDerivAt_polyaH (t : ℝ) :
    HasDerivAt polyaH (4 / Real.pi * Real.exp (-t ^ 2 / 2) - 1) t := by
  unfold polyaH
  have h1 : HasDerivAt (fun x ↦ 2 * stdNormalCDF x - 1) (2 * stdNormalPDF t) t := by
    simpa using ((hasDerivAt_stdNormalCDF t).const_mul 2).sub_const 1
  have h2 := (h1.const_mul (4 / Real.sqrt (2 * Real.pi))).sub (hasDerivAt_id' t)
  refine h2.congr_deriv ?_
  rw [stdNormalPDF_eq]
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp [hpi, hsqrt]
  rw [hsq]
  ring

private lemma hasDerivAt_polyaG (t : ℝ) :
    HasDerivAt polyaG (Real.exp (-t ^ 2 / 2) * polyaH t) t := by
  unfold polyaG
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-x ^ 2 / 2)) (-t * Real.exp (-t ^ 2 / 2)) t := by
    have hq : HasDerivAt (fun x : ℝ ↦ -x ^ 2 / 2) (-t) t := by
      convert (hasDerivAt_pow 2 t).fun_neg.div_const (2 : ℝ) using 1
      ring
    convert hq.exp using 1
    ring
  have hcdf1 : HasDerivAt (fun x ↦ 4 * stdNormalCDF x) (4 * stdNormalPDF t) t :=
    (hasDerivAt_stdNormalCDF t).const_mul 4
  have hcdf2 : HasDerivAt (fun x ↦ 1 - stdNormalCDF x) (-stdNormalPDF t) t := by
    simpa using (hasDerivAt_stdNormalCDF t).const_sub 1
  refine (hexp.sub (hcdf1.mul hcdf2)).congr_deriv ?_
  unfold polyaH
  rw [stdNormalPDF_eq]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp [hsqrt]
  ring

private lemma polyaH_deriv_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    4 / Real.pi * Real.exp (-b ^ 2 / 2) - 1 ≤ 4 / Real.pi * Real.exp (-a ^ 2 / 2) - 1 := by
  have hexp : Real.exp (-b ^ 2 / 2) ≤ Real.exp (-a ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith [mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 4 / Real.pi)]

private lemma tendsto_polyaG_atTop : Tendsto polyaG atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ ↦ Real.exp (-t ^ 2 / 2)) atTop (𝓝 0) := by
    have hmul := tendsto_stdNormalPDF_atTop.const_mul (Real.sqrt (2 * Real.pi))
    rw [mul_zero] at hmul
    refine hmul.congr fun t ↦ ?_
    rw [stdNormalPDF_eq, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have h2 : Tendsto (fun t : ℝ ↦ 4 * stdNormalCDF t * (1 - stdNormalCDF t)) atTop (𝓝 0) := by
    have ha : Tendsto (fun t : ℝ ↦ 4 * stdNormalCDF t) atTop (𝓝 (4 * 1)) :=
      tendsto_stdNormalCDF_atTop.const_mul 4
    have hb : Tendsto (fun t : ℝ ↦ 1 - stdNormalCDF t) atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub tendsto_stdNormalCDF_atTop
    simpa using ha.mul hb
  unfold polyaG
  simpa using h1.sub h2

private lemma polyaG_nonneg_of_pos {w : ℝ} (hw : 0 < w) : 0 ≤ polyaG w := by
  have hG0 : polyaG 0 = 0 := by
    unfold polyaG
    rw [stdNormalCDF_zero]
    norm_num
  have hH0 : polyaH 0 = 0 := by
    unfold polyaH
    rw [stdNormalCDF_zero]
    norm_num
  have hG_cont : Continuous polyaG :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_polyaG t).continuousAt
  have hH_cont : Continuous polyaH :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_polyaH t).continuousAt
  rcases le_total 0 (polyaH w) with hHw | hHw
  · have hH_nonneg : ∀ t ∈ Ioo 0 w, 0 ≤ polyaH t := by
      intro t ht
      by_contra hlt
      push Not at hlt
      obtain ⟨c₁, hc₁, hslope₁⟩ := exists_hasDerivAt_eq_slope polyaH _ ht.1
        hH_cont.continuousOn (fun x _ ↦ hasDerivAt_polyaH x)
      obtain ⟨c₂, hc₂, hslope₂⟩ := exists_hasDerivAt_eq_slope polyaH _ ht.2
        hH_cont.continuousOn (fun x _ ↦ hasDerivAt_polyaH x)
      have hneg₁ : 4 / Real.pi * Real.exp (-c₁ ^ 2 / 2) - 1 < 0 := by
        rw [hslope₁, hH0, sub_zero, sub_zero]
        exact div_neg_of_neg_of_pos hlt ht.1
      have hpos₂ : 0 < 4 / Real.pi * Real.exp (-c₂ ^ 2 / 2) - 1 := by
        rw [hslope₂]
        exact div_pos (by linarith) (sub_pos.mpr ht.2)
      have hanti := polyaH_deriv_antitone hc₁.1.le (hc₁.2.trans hc₂.1).le
      linarith
    have hmono : MonotoneOn polyaG (Icc 0 w) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 w) hG_cont.continuousOn
        (fun t _ ↦ (hasDerivAt_polyaG t).hasDerivWithinAt) fun t ht ↦ ?_
      rw [interior_Icc] at ht
      exact mul_nonneg (Real.exp_pos _).le (hH_nonneg t ht)
    rw [← hG0]
    exact hmono (left_mem_Icc.mpr hw.le) (right_mem_Icc.mpr hw.le) hw.le
  · have hH'w : 4 / Real.pi * Real.exp (-w ^ 2 / 2) - 1 ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have hsmono : StrictMonoOn polyaH (Icc 0 w) := by
        refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 w) hH_cont.continuousOn
          (fun t _ ↦ (hasDerivAt_polyaH t).hasDerivWithinAt) fun t ht ↦ ?_
        rw [interior_Icc] at ht
        exact lt_of_lt_of_le hpos (polyaH_deriv_antitone ht.1.le ht.2.le)
      have hlt : polyaH 0 < polyaH w :=
        hsmono (left_mem_Icc.mpr hw.le) (right_mem_Icc.mpr hw.le) hw
      linarith
    have hH_anti : AntitoneOn polyaH (Ici w) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici w) hH_cont.continuousOn
        (fun t _ ↦ (hasDerivAt_polyaH t).hasDerivWithinAt) fun t ht ↦ ?_
      rw [interior_Ici] at ht
      exact (polyaH_deriv_antitone hw.le (mem_Ioi.mp ht).le).trans hH'w
    have hG_anti : AntitoneOn polyaG (Ici w) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici w) hG_cont.continuousOn
        (fun t _ ↦ (hasDerivAt_polyaG t).hasDerivWithinAt) fun t ht ↦ ?_
      rw [interior_Ici] at ht
      have hHt : polyaH t ≤ 0 :=
        (hH_anti self_mem_Ici (mem_Ici.mpr (mem_Ioi.mp ht).le) (mem_Ioi.mp ht).le).trans hHw
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hHt
    refine le_of_tendsto tendsto_polyaG_atTop ?_
    filter_upwards [eventually_ge_atTop w] with t ht
    exact hG_anti self_mem_Ici ht ht

/-- Pólya–Chu normal product inequality $4\Phi(w)(1 - \Phi(w)) \le e^{-w^2/2}$
(used in Lemma 3.25 `\label{lem91}`, `SteinIntro.tex:1677-1686`). -/
theorem four_mul_stdNormalCDF_mul_one_sub_le_exp (w : ℝ) :
    4 * stdNormalCDF w * (1 - stdNormalCDF w) ≤ Real.exp (-w ^ 2 / 2) := by
  have hnonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ polyaG u := fun u hu ↦ by
    rcases hu.eq_or_lt with rfl | hpos
    · unfold polyaG
      rw [stdNormalCDF_zero]
      norm_num
    · exact polyaG_nonneg_of_pos hpos
  rcases le_total 0 w with hw | hw
  · have h := hnonneg w hw
    unfold polyaG at h
    linarith
  · have h := hnonneg (-w) (neg_nonneg.mpr hw)
    unfold polyaG at h
    rw [stdNormalCDF_neg] at h
    have hexp : Real.exp (-(-w) ^ 2 / 2) = Real.exp (-w ^ 2 / 2) := by ring_nf
    rw [hexp] at h
    linarith

/-- Pólya–Chu bound in PDF ratio form: $\Phi(w)(1 - \Phi(w)) / \phi(w) \le \sqrt{2\pi} / 4$
(Lemma 3.25 `\label{lem91}`, `SteinIntro.tex:1677-1686`). -/
theorem stdNormalCDF_mul_one_sub_div_pdf_le (w : ℝ) :
    stdNormalCDF w * (1 - stdNormalCDF w) / stdNormalPDF w ≤ Real.sqrt (2 * Real.pi) / 4 := by
  rw [div_le_iff₀ (stdNormalPDF_pos w), stdNormalPDF_eq]
  have h := four_mul_stdNormalCDF_mul_one_sub_le_exp w
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hmul :
      Real.sqrt (2 * Real.pi) / 4 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2)) =
        Real.exp (-w ^ 2 / 2) / 4 := by
    field_simp [hsqrt]
  rw [hmul]
  linarith

/-- Comparison $\sqrt{2\pi}/4 \le \sqrt{\pi/2}$ between the sharp and printed constants in
Lemma 3.25 (`\label{lem91}`, `SteinIntro.tex:1677-1686`). -/
theorem sqrt_two_pi_div_four_le_sqrt_pi_div_two :
    Real.sqrt (2 * Real.pi) / 4 ≤ Real.sqrt (Real.pi / 2) := by
  have h4 : (4 : ℝ) = Real.sqrt 16 := by
    symm
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  rw [h4, ← Real.sqrt_div (by positivity)]
  exact Real.sqrt_le_sqrt (by linarith [Real.pi_pos])

/-- Bound $\sqrt{2\pi}/4 \le 1$ used in Theorem 3.28 (`\label{thm92}`, `SteinIntro.tex:1778`). -/
theorem sqrt_two_pi_div_four_le_one : Real.sqrt (2 * Real.pi) / 4 ≤ 1 := by
  have h4 : (4 : ℝ) = Real.sqrt 16 := by
    symm
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have hle : Real.sqrt (2 * Real.pi) ≤ 4 := by
    rw [h4]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
  linarith

/-! ### Section 2: Unified Bounds for Antitone `[0, 1]` Stein Solutions -/

section AntitoneBounds

private lemma stdNormalPDF_mul_normalSteinSol_eq_right {h : ℝ → ℝ}
    (hInt : Integrable h stdNormalLaw) (w : ℝ) :
    stdNormalPDF w * normalSteinSol h w =
      stdNormalExpect h * (1 - stdNormalCDF w) -
        ∫ t in Ioi w, stdNormalPDF t * h t := by
  have hexp_pdf : ∀ t : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) =
      stdNormalPDF t := fun t ↦ (stdNormalPDF_eq t).symm
  have hexp_cancel : Real.exp (-w ^ 2 / 2) * Real.exp (w ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpdf_h : Integrable (fun t ↦ stdNormalPDF t * h t) volume :=
    integrable_stdNormalLaw_iff.mp hInt
  calc
    stdNormalPDF w * normalSteinSol h w
      = (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-w ^ 2 / 2) * Real.exp (w ^ 2 / 2)) *
          ∫ t in Ioi w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t) := by
        rw [stdNormalPDF_eq, normalSteinSol]; ring
    _ = ∫ t in Ioi w, (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) := by
        rw [hexp_cancel, mul_one, ← integral_const_mul]
    _ = ∫ t in Ioi w, (stdNormalPDF t * stdNormalExpect h - stdNormalPDF t * h t) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
        rw [← hexp_pdf t]; ring
    _ = stdNormalExpect h * (1 - stdNormalCDF w) - ∫ t in Ioi w, stdNormalPDF t * h t := by
        rw [integral_sub (integrable_stdNormalPDF.mul_const _).integrableOn hpdf_h.integrableOn,
          integral_mul_const, ← one_sub_stdNormalCDF_eq_integral_Ioi]
        ring

private lemma stdNormalPDF_mul_normalSteinSol_eq_left {h : ℝ → ℝ}
    (hInt : Integrable h stdNormalLaw) (w : ℝ) :
    stdNormalPDF w * normalSteinSol h w =
      (∫ t in Iic w, stdNormalPDF t * h t) - stdNormalExpect h * stdNormalCDF w := by
  have hpdf_h : Integrable (fun t ↦ stdNormalPDF t * h t) volume :=
    integrable_stdNormalLaw_iff.mp hInt
  have htot : (∫ t in Iic w, stdNormalPDF t * h t) + ∫ t in Ioi w, stdNormalPDF t * h t =
      stdNormalExpect h := by
    rw [← compl_Iic, integral_add_compl measurableSet_Iic hpdf_h,
      ← stdNormalExpect_eq_integral_mul_pdf]
  rw [stdNormalPDF_mul_normalSteinSol_eq_right hInt w]
  linarith

private lemma stdNormalPDF_mul_normalSteinSol_eq_split {h : ℝ → ℝ}
    (hInt : Integrable h stdNormalLaw) (w : ℝ) :
    stdNormalPDF w * normalSteinSol h w =
      (∫ t in Iic w, stdNormalPDF t * h t) * (1 - stdNormalCDF w) -
        stdNormalCDF w * ∫ t in Ioi w, stdNormalPDF t * h t := by
  have hpdf_h : Integrable (fun t ↦ stdNormalPDF t * h t) volume :=
    integrable_stdNormalLaw_iff.mp hInt
  have htot : stdNormalExpect h =
      (∫ t in Iic w, stdNormalPDF t * h t) + ∫ t in Ioi w, stdNormalPDF t * h t := by
    rw [stdNormalExpect_eq_integral_mul_pdf, ← compl_Iic,
      integral_add_compl measurableSet_Iic hpdf_h]
  rw [stdNormalPDF_mul_normalSteinSol_eq_right hInt w, htot]
  ring

private lemma antitone_mem_Icc_normalSteinSol_bounds {h : ℝ → ℝ}
    (hMeas : Measurable h) (hAnti : Antitone h) (hIcc : ∀ t : ℝ, 0 ≤ h t ∧ h t ≤ 1) (w : ℝ) :
    0 ≤ normalSteinSol h w ∧
      normalSteinSol h w ≤ Real.sqrt (2 * Real.pi) / 4 ∧
      |w * normalSteinSol h w + h w - stdNormalExpect h| ≤ 1 := by
  have hInt : Integrable h stdNormalLaw :=
    Integrable.of_bound hMeas.aestronglyMeasurable 1 (ae_of_all _ fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hIcc t).1]; exact (hIcc t).2)
  have hpdf_h : Integrable (fun t ↦ stdNormalPDF t * h t) volume :=
    integrable_stdNormalLaw_iff.mp hInt
  have hc_nn : 0 ≤ stdNormalExpect h :=
    integral_nonneg fun t ↦ (hIcc t).1
  have hc_le : stdNormalExpect h ≤ 1 := by
    calc stdNormalExpect h = ∫ t, h t ∂stdNormalLaw := rfl
      _ ≤ ∫ _, (1 : ℝ) ∂stdNormalLaw :=
          integral_mono hInt (integrable_const 1) fun t ↦ (hIcc t).2
      _ = 1 := by simp
  have hIic_ge : h w * stdNormalCDF w ≤ ∫ t in Iic w, stdNormalPDF t * h t := by
    rw [stdNormalCDF_eq_integral_Iic, ← integral_const_mul]
    refine setIntegral_mono_on (integrable_stdNormalPDF.const_mul _).integrableOn
      hpdf_h.integrableOn measurableSet_Iic fun t ht ↦ ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hAnti ht) (stdNormalPDF_nonneg t)
  have hIic_le : (∫ t in Iic w, stdNormalPDF t * h t) ≤ stdNormalCDF w := by
    rw [stdNormalCDF_eq_integral_Iic]
    refine setIntegral_mono_on hpdf_h.integrableOn integrable_stdNormalPDF.integrableOn
      measurableSet_Iic fun t _ ↦ ?_
    exact mul_le_of_le_one_right (stdNormalPDF_nonneg t) (hIcc t).2
  have hIoi_le : (∫ t in Ioi w, stdNormalPDF t * h t) ≤ h w * (1 - stdNormalCDF w) := by
    rw [one_sub_stdNormalCDF_eq_integral_Ioi, ← integral_const_mul]
    refine setIntegral_mono_on hpdf_h.integrableOn
      (integrable_stdNormalPDF.const_mul _).integrableOn measurableSet_Ioi fun t ht ↦ ?_
    rw [mul_comm (h w)]
    exact mul_le_mul_of_nonneg_left (hAnti (le_of_lt ht)) (stdNormalPDF_nonneg t)
  have hIoi_nn : 0 ≤ ∫ t in Ioi w, stdNormalPDF t * h t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ ↦
      mul_nonneg (stdNormalPDF_nonneg t) (hIcc t).1
  have hsplit := stdNormalPDF_mul_normalSteinSol_eq_split hInt w
  have hcdf_nn := stdNormalCDF_nonneg w
  have h1sub_nn : 0 ≤ 1 - stdNormalCDF w := sub_nonneg.mpr (stdNormalCDF_le_one w)
  have hfw_nn : 0 ≤ normalSteinSol h w := by
    have hprod_nn : 0 ≤ stdNormalPDF w * normalSteinSol h w := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_right hIic_ge h1sub_nn,
        mul_le_mul_of_nonneg_left hIoi_le hcdf_nn]
    exact nonneg_of_mul_nonneg_right hprod_nn (stdNormalPDF_pos w)
  have hfw_le : normalSteinSol h w ≤ Real.sqrt (2 * Real.pi) / 4 := by
    have hprod_le : stdNormalPDF w * normalSteinSol h w ≤
        stdNormalCDF w * (1 - stdNormalCDF w) := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_right hIic_le h1sub_nn,
        mul_nonneg hcdf_nn hIoi_nn]
    have hdiv : normalSteinSol h w ≤
        stdNormalCDF w * (1 - stdNormalCDF w) / stdNormalPDF w := by
      rw [le_div_iff₀ (stdNormalPDF_pos w), mul_comm]
      exact hprod_le
    exact hdiv.trans (stdNormalCDF_mul_one_sub_div_pdf_le w)
  refine ⟨hfw_nn, hfw_le, ?_⟩
  rw [abs_le]
  rcases le_total 0 w with hw | hw
  · constructor
    · nlinarith [mul_nonneg hw hfw_nn, (hIcc w).1]
    · have hright := stdNormalPDF_mul_normalSteinSol_eq_right hInt w
      have h1 : stdNormalPDF w * normalSteinSol h w ≤
          stdNormalExpect h * (1 - stdNormalCDF w) := by linarith
      have h2 : w * (stdNormalPDF w * normalSteinSol h w) ≤
          stdNormalExpect h * (w * (1 - stdNormalCDF w)) := by
        have := mul_le_mul_of_nonneg_left h1 hw
        linarith
      have h3 : stdNormalExpect h * (w * (1 - stdNormalCDF w)) ≤
          stdNormalExpect h * stdNormalPDF w :=
        mul_le_mul_of_nonneg_left (mul_one_sub_stdNormalCDF_le w hw) hc_nn
      have hwf : w * normalSteinSol h w ≤ stdNormalExpect h := by
        have hpdf_pos := stdNormalPDF_pos w
        nlinarith
      linarith [(hIcc w).2]
  · constructor
    · have hleft := stdNormalPDF_mul_normalSteinSol_eq_left hInt w
      have h1 : stdNormalPDF w * normalSteinSol h w ≤
          (1 - stdNormalExpect h) * stdNormalCDF w := by linarith
      have h2 : (-w) * (stdNormalPDF w * normalSteinSol h w) ≤
          (1 - stdNormalExpect h) * ((-w) * stdNormalCDF w) := by
        have := mul_le_mul_of_nonneg_left h1 (neg_nonneg.mpr hw)
        linarith
      have h3 : (1 - stdNormalExpect h) * ((-w) * stdNormalCDF w) ≤
          (1 - stdNormalExpect h) * stdNormalPDF w :=
        mul_le_mul_of_nonneg_left (neg_mul_stdNormalCDF_le w hw) (sub_nonneg.mpr hc_le)
      have hwf : stdNormalExpect h - 1 ≤ w * normalSteinSol h w := by
        have hpdf_pos := stdNormalPDF_pos w
        nlinarith
      linarith [(hIcc w).1]
    · have hw_nonpos : w * normalSteinSol h w ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hw hfw_nn
      linarith [(hIcc w).2]

private lemma abs_mul_sub_mul_le_of_lipschitzWith_one {f : ℝ → ℝ}
    (hf_bdd : ∀ z : ℝ, |f z| ≤ Real.sqrt (2 * Real.pi) / 4)
    (hf_lip : LipschitzWith 1 f) (u v w : ℝ) :
    |(w + u) * f (w + u) - (w + v) * f (w + v)| ≤
      (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|) := by
  have hstep : ∀ z : ℝ, |(w + z) * f (w + z) - w * f w| ≤
      (|w| + Real.sqrt (2 * Real.pi) / 4) * |z| := fun z ↦ by
    have hlip : |f (w + z) - f w| ≤ |z| := by
      have hd := hf_lip.dist_le_mul (w + z) w
      simpa [Real.dist_eq] using hd
    calc
      |(w + z) * f (w + z) - w * f w|
        = |w * (f (w + z) - f w) + z * f (w + z)| := by ring_nf
      _ ≤ |w * (f (w + z) - f w)| + |z * f (w + z)| := abs_add_le _ _
      _ = |w| * |f (w + z) - f w| + |z| * |f (w + z)| := by rw [abs_mul, abs_mul]
      _ ≤ |w| * |z| + |z| * (Real.sqrt (2 * Real.pi) / 4) :=
          add_le_add (mul_le_mul_of_nonneg_left hlip (abs_nonneg w))
            (mul_le_mul_of_nonneg_left (hf_bdd (w + z)) (abs_nonneg z))
      _ = (|w| + Real.sqrt (2 * Real.pi) / 4) * |z| := by ring
  calc
    |(w + u) * f (w + u) - (w + v) * f (w + v)|
      = |((w + u) * f (w + u) - w * f w) - ((w + v) * f (w + v) - w * f w)| := by ring_nf
    _ ≤ |(w + u) * f (w + u) - w * f w| + |(w + v) * f (w + v) - w * f w| := abs_sub _ _
    _ ≤ (|w| + Real.sqrt (2 * Real.pi) / 4) * |u| +
          (|w| + Real.sqrt (2 * Real.pi) / 4) * |v| := add_le_add (hstep u) (hstep v)
    _ = (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|) := by ring

end AntitoneBounds

/-! ### Section 3: Theorem 3.24 (Corrected) and Lemma 3.25 (Corrected) -/

/-- **Theorem 3.24 (corrected)** (`\label{thm91}`, eq. `(3.38)` `\label{91}`,
`SteinIntro.tex:1666-1675`; `ISSUE-2.2`, ruling `D4`): for any real-valued random variable $W$
(`AEMeasurable W P`, no moment hypothesis needed) and standard normal $Z \sim \mathcal{N}(0, 1)$,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) =
\sup_{x \in \mathbb{R}} |\mathbb{E}[D_- f_x(W) - W f_x(W)]|$. -/
theorem kolmogorovDist_map_stdNormal_eq_iSup_normalSteinOpLeft
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (hW : AEMeasurable W P) (_hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) =
      ⨆ x : ℝ, ENNReal.ofReal |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P| := by
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  rw [hZ_law, kolmogorovDist_eq_iSup]
  refine iSup_congr fun x ↦ ?_
  have hmapW : (P.map W).real (Iic x) = P.real {ω | W ω ≤ x} :=
    map_measureReal_apply_of_aemeasurable hW measurableSet_Iic
  have hmapZ : stdNormalLaw.real (Iic x) = stdNormalCDF x :=
    (cdf_eq_real stdNormalLaw x).symm
  rw [hmapW, hmapZ, abs_measureReal_Iic_sub_stdNormalCDF_eq P hW x]

private lemma antitone_indicator_Iic (x : ℝ) : Antitone ((Iic x).indicator (1 : ℝ → ℝ)) := by
  intro a b hab
  by_cases hb : b ∈ Iic x
  · have ha : a ∈ Iic x := hab.trans hb
    simp [ha, hb]
  · by_cases ha : a ∈ Iic x
    · simp [ha, hb]
    · simp [ha, hb]

private lemma indicator_Iic_mem_Icc (x t : ℝ) :
    0 ≤ (Iic x).indicator (1 : ℝ → ℝ) t ∧ (Iic x).indicator (1 : ℝ → ℝ) t ≤ 1 := by
  by_cases ht : t ∈ Iic x <;> simp [ht]

/-- Nonnegativity $0 \le f_x(w)$ of `normalSteinSolKolm x`
(Lemma 3.25 `\label{lem91}`, `SteinIntro.tex:1677-1686`). -/
theorem normalSteinSolKolm_nonneg (x w : ℝ) : 0 ≤ normalSteinSolKolm x w :=
  (antitone_mem_Icc_normalSteinSol_bounds (measurable_one.indicator measurableSet_Iic)
    (antitone_indicator_Iic x) (indicator_Iic_mem_Icc x) w).1

/-- Sharp supremum bound $|f_x(w)| \le \sqrt{2\pi}/4$ on `normalSteinSolKolm x`
(CGS 2011 Lemma 2.3; Lemma 3.25 `\label{lem91}`, `SteinIntro.tex:1677-1686`). -/
theorem abs_normalSteinSolKolm_le_sqrt_two_pi_div_four (x w : ℝ) :
    |normalSteinSolKolm x w| ≤ Real.sqrt (2 * Real.pi) / 4 := by
  have hb := antitone_mem_Icc_normalSteinSol_bounds (measurable_one.indicator measurableSet_Iic)
    (antitone_indicator_Iic x) (indicator_Iic_mem_Icc x) w
  rw [normalSteinSolKolm, abs_of_nonneg hb.1]
  exact hb.2.1

/-- Sharp left-derivative bound $|D_- f_x(w)| \le 1$ on `normalSteinSolKolm x`, used in the proof
of Theorem 3.28 (`\label{thm92}`, `SteinIntro.tex:1768`; `ISSUE-3.25`). -/
theorem abs_derivWithin_Iic_normalSteinSolKolm_le_one (x w : ℝ) :
    |derivWithin (normalSteinSolKolm x) (Iic w) w| ≤ 1 := by
  have hd := (hasDerivWithinAt_Iic_normalSteinSolKolm x w).derivWithin (uniqueDiffWithinAt_Iic w)
  have hb := (antitone_mem_Icc_normalSteinSol_bounds (measurable_one.indicator measurableSet_Iic)
    (antitone_indicator_Iic x) (indicator_Iic_mem_Icc x) w).2.2
  rw [hd, ← stdNormalExpect_indicator_Iic, normalSteinSolKolm]
  exact hb

/-- `normalSteinSolKolm x` is $1$-Lipschitz on $\mathbb{R}$
(CGS 2011 Lemma 2.3; Lemma 3.25 `\label{lem91}`, `SteinIntro.tex:1677-1686`). -/
theorem lipschitzWith_one_normalSteinSolKolm (x : ℝ) :
    LipschitzWith 1 (normalSteinSolKolm x) := by
  set f := normalSteinSolKolm x
  have hf_cont : Continuous f := continuous_normalSteinSolKolm x
  have hno_x : ∀ a b : ℝ, a < b → (∀ c ∈ Ioo a b, c ≠ x) → |f b - f a| ≤ b - a := by
    intro a b hab hne
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f _ hab hf_cont.continuousOn
      fun c hc ↦ hasDerivAt_normalSteinSolKolm_of_ne x (hne c hc)
    have hc_le : |c * f c + (Iic x).indicator 1 c - stdNormalCDF x| ≤ 1 := by
      have hb := (antitone_mem_Icc_normalSteinSol_bounds
        (measurable_one.indicator measurableSet_Iic)
        (antitone_indicator_Iic x) (indicator_Iic_mem_Icc x) c).2.2
      rwa [stdNormalExpect_indicator_Iic] at hb
    have hdiv : |f b - f a| / (b - a) ≤ 1 := by
      rw [← abs_of_pos (sub_pos.mpr hab), ← abs_div, ← hslope]
      exact hc_le
    rwa [div_le_one (sub_pos.mpr hab)] at hdiv
  have hord : ∀ a b : ℝ, a ≤ b → |f b - f a| ≤ b - a := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hlt
    · simp
    · by_cases hbx : b ≤ x
      · exact hno_x a b hlt fun c hc ↦ (hc.2.trans_le hbx).ne
      · by_cases hxa : x ≤ a
        · exact hno_x a b hlt fun c hc ↦ (hxa.trans_lt hc.1).ne'
        · push Not at hbx hxa
          have h1 := hno_x a x hxa fun c hc ↦ hc.2.ne
          have h2 := hno_x x b hbx fun c hc ↦ hc.1.ne'
          calc |f b - f a| = |(f b - f x) + (f x - f a)| := by ring_nf
            _ ≤ |f b - f x| + |f x - f a| := abs_add_le _ _
            _ ≤ (b - x) + (x - a) := add_le_add h2 h1
            _ = b - a := by ring
  refine LipschitzWith.mk_one fun u v ↦ ?_
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm (f u), abs_sub_comm u v, abs_of_nonneg (sub_nonneg.mpr huv)]
    exact hord u v huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hord v u hvu

/-- Third inequality of Lemma 3.25 (`\label{lem91}`, `SteinIntro.tex:1683-1685`):
$|(w + u) f_x(w + u) - (w + v) f_x(w + v)| \le (|w| + \sqrt{2\pi}/4)(|u| + |v|)$. -/
theorem abs_mul_normalSteinSolKolm_sub_le (x u v w : ℝ) :
    |(w + u) * normalSteinSolKolm x (w + u) - (w + v) * normalSteinSolKolm x (w + v)| ≤
      (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|) :=
  abs_mul_sub_mul_le_of_lipschitzWith_one (abs_normalSteinSolKolm_le_sqrt_two_pi_div_four x)
    (lipschitzWith_one_normalSteinSolKolm x) u v w

/-- **Lemma 3.25 (corrected)** (`\label{lem91}`, `SteinIntro.tex:1677-1686`; `ISSUE-2.2`,
`ISSUE-3.25`, ruling `D4`): the printed bounds $\|f_x\| \le \sqrt{\pi/2}$, $\|D_- f_x\| \le 2$,
and $|(w + u)f_x(w + u) - (w + v)f_x(w + v)| \le (|w| + \sqrt{2\pi}/4)(|u| + |v|)$ hold for every
$x \in \mathbb{R}$. -/
theorem lem3_25_corrected_bounds (x : ℝ) :
    (∀ w : ℝ, |normalSteinSolKolm x w| ≤ Real.sqrt (Real.pi / 2)) ∧
    (∀ w : ℝ, |derivWithin (normalSteinSolKolm x) (Iic w) w| ≤ 2) ∧
    (∀ u v w : ℝ,
      |(w + u) * normalSteinSolKolm x (w + u) - (w + v) * normalSteinSolKolm x (w + v)| ≤
        (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|)) :=
  ⟨abs_normalSteinSolKolm_le x,
    fun w ↦ (abs_derivWithin_Iic_normalSteinSolKolm_le_one x w).trans (by norm_num),
    abs_mul_normalSteinSolKolm_sub_le x⟩

/-! ### Section 4: Ramp Smoothing and Corollary 3.26 (`Cor3_26`) -/

/-- Continuous piecewise-linear ramp smoothing $\mathbb{I}[\cdot \le x]$ on $[x, x + \varepsilon]$
(used to prove Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
noncomputable def kolmSmoothInd (x ε t : ℝ) : ℝ :=
  min 1 (max 0 ((x + ε - t) / ε))

private lemma continuous_kolmSmoothInd (x ε : ℝ) : Continuous (kolmSmoothInd x ε) := by
  unfold kolmSmoothInd
  fun_prop

private lemma antitone_kolmSmoothInd (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Antitone (kolmSmoothInd x ε) := by
  intro a b hab
  unfold kolmSmoothInd
  refine min_le_min_left 1 (max_le_max_left 0 ?_)
  exact div_le_div_of_nonneg_right (by linarith) hε.le

private lemma kolmSmoothInd_mem_Icc (x : ℝ) {ε : ℝ} (_ : 0 < ε) (t : ℝ) :
    0 ≤ kolmSmoothInd x ε t ∧ kolmSmoothInd x ε t ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩

private lemma indicator_Iic_le_kolmSmoothInd (x : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (Iic x).indicator (1 : ℝ → ℝ) t ≤ kolmSmoothInd x ε t := by
  by_cases ht : t ∈ Iic x
  · rw [Set.indicator_of_mem ht, Pi.one_apply]
    unfold kolmSmoothInd
    have h1 : 1 ≤ (x + ε - t) / ε := by
      rw [le_div_iff₀ hε]
      linarith [mem_Iic.mp ht]
    exact le_min le_rfl (h1.trans (le_max_right 0 _))
  · rw [Set.indicator_of_notMem ht]
    exact (kolmSmoothInd_mem_Icc x hε t).1

private lemma kolmSmoothInd_le_indicator_Iic_add (x : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    kolmSmoothInd x ε t ≤ (Iic (x + ε)).indicator (1 : ℝ → ℝ) t := by
  by_cases ht : t ∈ Iic (x + ε)
  · rw [Set.indicator_of_mem ht, Pi.one_apply]
    exact (kolmSmoothInd_mem_Icc x hε t).2
  · rw [Set.indicator_of_notMem ht]
    unfold kolmSmoothInd
    have hneg : (x + ε - t) / ε ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp (mem_Iic.not.mp ht)]) hε.le
    rw [max_eq_left hneg, min_eq_right zero_le_one]

/-- For every $x \in \mathbb{R}$ and $\varepsilon > 0$, the smoothed Kolmogorov Stein solution
`normalSteinSol (kolmSmoothInd x ε)` belongs to `normalKolmogorovClass`
(Corollary 3.26 `\label{cor91}`, `SteinIntro.tex:1688-1694`). -/
theorem normalSteinSol_kolmSmoothInd_mem_normalKolmogorovClass (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    normalSteinSol (kolmSmoothInd x ε) ∈ normalKolmogorovClass := by
  set h := kolmSmoothInd x ε
  set f := normalSteinSol h
  have hCont : Continuous h := continuous_kolmSmoothInd x ε
  have hAnti : Antitone h := antitone_kolmSmoothInd x hε
  have hIcc : ∀ t : ℝ, 0 ≤ h t ∧ h t ≤ 1 := kolmSmoothInd_mem_Icc x hε
  have hInt : Integrable h stdNormalLaw :=
    Integrable.of_bound hCont.aestronglyMeasurable 1 (ae_of_all _ fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hIcc t).1]; exact (hIcc t).2)
  have hf_deriv : ∀ w : ℝ, HasDerivAt f (w * f w + h w - stdNormalExpect h) w :=
    hasDerivAt_normalSteinSol_of_continuous hInt hCont
  have hf_diff : Differentiable ℝ f := fun w ↦ (hf_deriv w).differentiableAt
  have hf_bdd_sharp : ∀ w : ℝ, |f w| ≤ Real.sqrt (2 * Real.pi) / 4 := fun w ↦ by
    have hb := antitone_mem_Icc_normalSteinSol_bounds hCont.measurable hAnti hIcc w
    rw [abs_of_nonneg hb.1]
    exact hb.2.1
  have hf_deriv_sharp : ∀ w : ℝ, |deriv f w| ≤ 1 := fun w ↦ by
    rw [(hf_deriv w).deriv]
    exact (antitone_mem_Icc_normalSteinSol_bounds hCont.measurable hAnti hIcc w).2.2
  have hf_lip : LipschitzWith 1 f := by
    refine lipschitzWith_of_nnnorm_deriv_le hf_diff fun w ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact hf_deriv_sharp w
  refine ⟨hf_diff,
    fun w ↦ (hf_bdd_sharp w).trans sqrt_two_pi_div_four_le_sqrt_pi_div_two,
    fun w ↦ (hf_deriv_sharp w).trans (by norm_num),
    abs_mul_sub_mul_le_of_lipschitzWith_one hf_bdd_sharp hf_lip⟩

/-- `stdNormalCDF` is Lipschitz with constant $(\sqrt{2\pi})^{-1}$:
$|\Phi(b) - \Phi(a)| \le |b - a| / \sqrt{2\pi}$
(used in Corollary 3.26 `\label{cor91}` and Theorem 3.27, `SteinIntro.tex:1718-1719`). -/
theorem abs_stdNormalCDF_sub_le (a b : ℝ) :
    |stdNormalCDF b - stdNormalCDF a| ≤ |b - a| / Real.sqrt (2 * Real.pi) := by
  set K : ℝ≥0 := ⟨(Real.sqrt (2 * Real.pi))⁻¹, by positivity⟩
  have hlip : LipschitzWith K stdNormalCDF := by
    refine lipschitzWith_of_nnnorm_deriv_le differentiable_stdNormalCDF fun w ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, deriv_stdNormalCDF,
      abs_of_nonneg (stdNormalPDF_nonneg w)]
    exact (stdNormalPDF_le_zero w).trans_eq stdNormalPDF_zero
  have hd := hlip.dist_le_mul b a
  rw [Real.dist_eq, Real.dist_eq, show (K : ℝ) = (Real.sqrt (2 * Real.pi))⁻¹ from rfl] at hd
  rwa [inv_mul_eq_div] at hd

/-- **Corollary 3.26** (`\label{cor91}`, `SteinIntro.tex:1688-1694`): if $W$ is an integrable
real-valued random variable and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]|$ over `normalKolmogorovClass`.

Reading note: $\mathcal{F}$ (`normalKolmogorovClass`) is read as the *differentiable* functions
satisfying the bounds of Lemma 3.25; this excludes $f_x$ itself and gives a smaller supremum, so
the theorem implies every weaker-regularity reading, proved by smoothing $\mathbb{I}[\cdot \le x]$
with a piecewise-linear ramp `kolmSmoothInd x ε`. -/
theorem kolmogorovDist_map_stdNormal_le_iSup_normalSteinOp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (hW : Integrable W P) (_hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ normalKolmogorovClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P| := by
  set S : ℝ≥0∞ := ⨆ f ∈ normalKolmogorovClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|
  have : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW.aemeasurable).mpr ‹_›
  rw [hZ_law, kolmogorovDist_eq_iSup]
  refine iSup_le fun x ↦ ?_
  have hmapW : (P.map W).real (Iic x) = P.real {ω | W ω ≤ x} :=
    map_measureReal_apply_of_aemeasurable hW.aemeasurable measurableSet_Iic
  have hmapZ : stdNormalLaw.real (Iic x) = stdNormalCDF x :=
    (cdf_eq_real stdNormalLaw x).symm
  rw [hmapW, hmapZ]
  have hprob_eq : ∀ y : ℝ, P.real {ω | W ω ≤ y} = ∫ ω, (Iic y).indicator 1 (W ω) ∂P := fun y ↦ by
    have hm : Measurable ((Iic y).indicator (1 : ℝ → ℝ)) :=
      measurable_one.indicator measurableSet_Iic
    have hmap_y : (P.map W).real (Iic y) = P.real {ω | W ω ≤ y} :=
      map_measureReal_apply_of_aemeasurable hW.aemeasurable measurableSet_Iic
    rw [← hmap_y, ← integral_map hW.aemeasurable hm.aestronglyMeasurable,
      integral_indicator_one measurableSet_Iic]
  have hint_ind : ∀ y : ℝ, Integrable (fun ω ↦ (Iic y).indicator (1 : ℝ → ℝ) (W ω)) P := fun y ↦
    Integrable.of_bound
      ((measurable_one.indicator measurableSet_Iic).comp_aemeasurable
        hW.aemeasurable).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by
        by_cases hω : W ω ≤ y <;> simp [mem_Iic, hω])
  have hstein_eq : ∀ y : ℝ, ∀ {ε : ℝ} (hε : 0 < ε),
      (∫ ω, kolmSmoothInd y ε (W ω) ∂P) - stdNormalExpect (kolmSmoothInd y ε) =
        ∫ ω, normalSteinOp (normalSteinSol (kolmSmoothInd y ε)) (W ω) ∂P := by
    intro y ε hε
    set h := kolmSmoothInd y ε
    have hCont := continuous_kolmSmoothInd y ε
    have hIcc := kolmSmoothInd_mem_Icc y hε
    have hIntN : Integrable h stdNormalLaw :=
      Integrable.of_bound hCont.aestronglyMeasurable 1 (ae_of_all _ fun t ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hIcc t).1]; exact (hIcc t).2)
    have hIntP : Integrable (fun ω ↦ h (W ω)) P :=
      Integrable.of_bound (hCont.comp_aestronglyMeasurable hW.aestronglyMeasurable) 1
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hIcc (W ω)).1]; exact (hIcc (W ω)).2)
    have hOp : ∀ u : ℝ, normalSteinOp (normalSteinSol h) u = h u - stdNormalExpect h := fun u ↦ by
      rw [normalSteinOp, (hasDerivAt_normalSteinSol_of_continuous hIntN hCont u).deriv]
      ring
    calc
      (∫ ω, h (W ω) ∂P) - stdNormalExpect h
        = (∫ ω, h (W ω) ∂P) - ∫ _ : Ω, stdNormalExpect h ∂P := by simp
      _ = ∫ ω, (h (W ω) - stdNormalExpect h) ∂P := (integral_sub hIntP (integrable_const _)).symm
      _ = ∫ ω, normalSteinOp (normalSteinSol h) (W ω) ∂P :=
          integral_congr_ae (ae_of_all _ fun ω ↦ (hOp (W ω)).symm)
  have hfor_eps : ∀ {ε : ℝ}, 0 < ε →
      ENNReal.ofReal |P.real {ω | W ω ≤ x} - stdNormalCDF x| ≤
        S + ENNReal.ofReal (ε / Real.sqrt (2 * Real.pi)) := by
    intro ε hε
    set h₁ := kolmSmoothInd x ε
    set f₁ := normalSteinSol h₁
    set h₂ := kolmSmoothInd (x - ε) ε
    set f₂ := normalSteinSol h₂
    have hf₁ : f₁ ∈ normalKolmogorovClass :=
      normalSteinSol_kolmSmoothInd_mem_normalKolmogorovClass x hε
    have hf₂ : f₂ ∈ normalKolmogorovClass :=
      normalSteinSol_kolmSmoothInd_mem_normalKolmogorovClass (x - ε) hε
    have hInt₁ : Integrable (fun ω ↦ h₁ (W ω)) P :=
      Integrable.of_bound ((continuous_kolmSmoothInd x ε).comp_aestronglyMeasurable
        hW.aestronglyMeasurable) 1 (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (kolmSmoothInd_mem_Icc x hε (W ω)).1]
          exact (kolmSmoothInd_mem_Icc x hε (W ω)).2)
    have hInt₂ : Integrable (fun ω ↦ h₂ (W ω)) P :=
      Integrable.of_bound ((continuous_kolmSmoothInd (x - ε) ε).comp_aestronglyMeasurable
        hW.aestronglyMeasurable) 1 (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (kolmSmoothInd_mem_Icc (x - ε) hε (W ω)).1]
          exact (kolmSmoothInd_mem_Icc (x - ε) hε (W ω)).2)
    have hIntN₁ : Integrable h₁ stdNormalLaw :=
      Integrable.of_bound (continuous_kolmSmoothInd x ε).aestronglyMeasurable 1
        (ae_of_all _ fun t ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (kolmSmoothInd_mem_Icc x hε t).1]
          exact (kolmSmoothInd_mem_Icc x hε t).2)
    have hIntN₂ : Integrable h₂ stdNormalLaw :=
      Integrable.of_bound (continuous_kolmSmoothInd (x - ε) ε).aestronglyMeasurable 1
        (ae_of_all _ fun t ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (kolmSmoothInd_mem_Icc (x - ε) hε t).1]
          exact (kolmSmoothInd_mem_Icc (x - ε) hε t).2)
    have hup_P : P.real {ω | W ω ≤ x} ≤ ∫ ω, h₁ (W ω) ∂P := by
      rw [hprob_eq x]
      exact integral_mono (hint_ind x) hInt₁ fun ω ↦ indicator_Iic_le_kolmSmoothInd x hε (W ω)
    have hup_Z : stdNormalExpect h₁ ≤ stdNormalCDF (x + ε) := by
      rw [← stdNormalExpect_indicator_Iic (x + ε)]
      exact integral_mono hIntN₁ ((integrable_const 1).indicator measurableSet_Iic)
        (kolmSmoothInd_le_indicator_Iic_add x hε)
    have hcdf_up : stdNormalCDF (x + ε) - stdNormalCDF x ≤ ε / Real.sqrt (2 * Real.pi) := by
      have h := abs_stdNormalCDF_sub_le x (x + ε)
      have heq : |(x + ε) - x| = ε := by rw [add_sub_cancel_left, abs_of_pos hε]
      rw [heq] at h
      exact (le_abs_self _).trans h
    have hpos_side : P.real {ω | W ω ≤ x} - stdNormalCDF x ≤
        |∫ ω, normalSteinOp f₁ (W ω) ∂P| + ε / Real.sqrt (2 * Real.pi) := by
      have hst := hstein_eq x hε
      linarith [le_abs_self (∫ ω, normalSteinOp f₁ (W ω) ∂P)]
    have hlo_P : (∫ ω, h₂ (W ω) ∂P) ≤ P.real {ω | W ω ≤ x} := by
      rw [hprob_eq x]
      refine integral_mono hInt₂ (hint_ind x) fun ω ↦ ?_
      have h := kolmSmoothInd_le_indicator_Iic_add (x - ε) hε (W ω)
      rwa [sub_add_cancel] at h
    have hlo_Z : stdNormalCDF (x - ε) ≤ stdNormalExpect h₂ := by
      rw [← stdNormalExpect_indicator_Iic (x - ε)]
      exact integral_mono ((integrable_const 1).indicator measurableSet_Iic) hIntN₂
        (indicator_Iic_le_kolmSmoothInd (x - ε) hε)
    have hcdf_lo : stdNormalCDF x - stdNormalCDF (x - ε) ≤ ε / Real.sqrt (2 * Real.pi) := by
      have h := abs_stdNormalCDF_sub_le (x - ε) x
      have heq : |x - (x - ε)| = ε := by rw [sub_sub_cancel, abs_of_pos hε]
      rw [heq] at h
      exact (le_abs_self _).trans h
    have hneg_side : stdNormalCDF x - P.real {ω | W ω ≤ x} ≤
        |∫ ω, normalSteinOp f₂ (W ω) ∂P| + ε / Real.sqrt (2 * Real.pi) := by
      have hst := hstein_eq (x - ε) hε
      linarith [neg_le_abs (∫ ω, normalSteinOp f₂ (W ω) ∂P)]
    rcases le_total 0 (P.real {ω | W ω ≤ x} - stdNormalCDF x) with hsign | hsign
    · rw [abs_of_nonneg hsign]
      calc ENNReal.ofReal (P.real {ω | W ω ≤ x} - stdNormalCDF x)
          ≤ ENNReal.ofReal (|∫ ω, normalSteinOp f₁ (W ω) ∂P| + ε / Real.sqrt (2 * Real.pi)) :=
            ENNReal.ofReal_le_ofReal hpos_side
        _ = ENNReal.ofReal |∫ ω, normalSteinOp f₁ (W ω) ∂P| +
              ENNReal.ofReal (ε / Real.sqrt (2 * Real.pi)) :=
            ENNReal.ofReal_add (abs_nonneg _) (by positivity)
        _ ≤ S + ENNReal.ofReal (ε / Real.sqrt (2 * Real.pi)) := by
            gcongr
            exact le_iSup₂_of_le f₁ hf₁ le_rfl
    · have habs : |P.real {ω | W ω ≤ x} - stdNormalCDF x| =
          stdNormalCDF x - P.real {ω | W ω ≤ x} := by
        rw [abs_of_nonpos hsign]; ring
      rw [habs]
      calc ENNReal.ofReal (stdNormalCDF x - P.real {ω | W ω ≤ x})
          ≤ ENNReal.ofReal (|∫ ω, normalSteinOp f₂ (W ω) ∂P| + ε / Real.sqrt (2 * Real.pi)) :=
            ENNReal.ofReal_le_ofReal hneg_side
        _ = ENNReal.ofReal |∫ ω, normalSteinOp f₂ (W ω) ∂P| +
              ENNReal.ofReal (ε / Real.sqrt (2 * Real.pi)) :=
            ENNReal.ofReal_add (abs_nonneg _) (by positivity)
        _ ≤ S + ENNReal.ofReal (ε / Real.sqrt (2 * Real.pi)) := by
            gcongr
            exact le_iSup₂_of_le f₂ hf₂ le_rfl
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  have hε_pos : 0 < (δ : ℝ) * Real.sqrt (2 * Real.pi) := by positivity
  have hbound := hfor_eps hε_pos
  have hcancel : (δ : ℝ) * Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi) = (δ : ℝ) :=
    mul_div_cancel_right₀ (δ : ℝ) (by positivity)
  rw [hcancel, ENNReal.ofReal_coe_nnreal] at hbound
  exact hbound

end SteinMethod
