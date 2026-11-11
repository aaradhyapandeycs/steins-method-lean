/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Metrics
import Formalization.Defs.NormalStein
import Formalization.Normal.MillRatio
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Kolmogorov Normal Stein Solution and IPM Identity (`Formalization.Normal.KolmogorovSolution`)

Develops the Kolmogorov normal Stein solution `normalSteinSolKolm`, its left-derivative Stein
characterization and uniqueness, machine-checked source-issue counterexamples for the two-sided
derivative reading, and the general integral probability metric Stein identity from Section 2 of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:578-670`):

* **Lemma 2.2 (corrected)** (`\label{lem2}`, `SteinIntro.tex:578-588`; `ISSUE-2.2`, `H3`, ruling
  `D4`): `normalSteinSolKolm_eq_neg_integral_Iic`, `abs_normalSteinSolKolm_le`,
  `bdd_normalSteinSolKolm`, `continuous_normalSteinSolKolm`,
  `hasDerivWithinAt_Iic_normalSteinSolKolm`, `normalSteinOpLeft_normalSteinSolKolm`,
  `hasDerivAt_normalSteinSolKolm_of_ne`, and `eq_normalSteinSolKolm_of_continuous_bounded`.
* **Source Issue `ISSUE-2.2` (Darboux no-solution & Dirac counterexample)**:
  `Lem2_2_twoSided_noSolution`, `not_differentiableAt_normalSteinSolKolm`, and
  `Cor2_3_twoSided_counterexample`.
* **Corollary 2.3 (corrected)** (`\label{cor1}`, `SteinIntro.tex:591-596`; ruling `D4`):
  `abs_measureReal_Iic_sub_stdNormalCDF_eq` (no moment hypothesis on `W`).
* **Proposition 2.4** (`\label{prop31}`, `SteinIntro.tex:665-670`; rulings `D1`, `D4`):
  `ipm_map_stdNormalLaw_eq_iSup_normalSteinOp`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace SteinMethod

/-! ### Private Calculus and Gaussian Integrability Helpers -/

section Helpers

private lemma kolm_exp_eq_sqrt_mul_pdf (t : ℝ) :
    Real.exp (-t ^ 2 / 2) = Real.sqrt (2 * Real.pi) * stdNormalPDF t := by
  rw [stdNormalPDF_eq, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

private lemma kolm_integrable_indicator_Iic (x : ℝ) :
    Integrable ((Set.Iic x).indicator (1 : ℝ → ℝ)) stdNormalLaw :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Iic

private lemma kolm_integrable_exp_mul {h : ℝ → ℝ} (hh : Integrable h stdNormalLaw) :
    Integrable (fun t ↦ Real.exp (-t ^ 2 / 2) * h t) volume := by
  refine ((integrable_stdNormalLaw_iff.mp hh).const_mul (Real.sqrt (2 * Real.pi))).congr
    (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [kolm_exp_eq_sqrt_mul_pdf]
  ring

private lemma kolm_integral_exp_mul {h : ℝ → ℝ} :
    (∫ t, Real.exp (-t ^ 2 / 2) * h t) = Real.sqrt (2 * Real.pi) * stdNormalExpect h := by
  simp_rw [kolm_exp_eq_sqrt_mul_pdf, mul_assoc]
  rw [integral_const_mul, ← stdNormalExpect_eq_integral_mul_pdf]

private lemma kolm_integrable_stein_integrand {h : ℝ → ℝ} (hh : Integrable h stdNormalLaw) :
    Integrable (fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) volume := by
  refine ((integrable_exp_neg_sq_div_two.mul_const (stdNormalExpect h)).sub
    (kolm_integrable_exp_mul hh)).congr (ae_of_all _ fun t ↦ ?_)
  simp only [Pi.sub_apply]
  ring

private lemma kolm_integral_stein_integrand_eq_zero {h : ℝ → ℝ}
    (hh : Integrable h stdNormalLaw) :
    (∫ t, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) = 0 := by
  have h1 := integrable_exp_neg_sq_div_two.mul_const (stdNormalExpect h)
  have h2 := kolm_integrable_exp_mul hh
  have heq : (fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) =
      fun t ↦ Real.exp (-t ^ 2 / 2) * stdNormalExpect h - Real.exp (-t ^ 2 / 2) * h t := by
    ext t
    ring
  rw [heq, integral_sub h1 h2, integral_mul_const, integral_exp_neg_sq_div_two,
    kolm_integral_exp_mul]
  ring

private lemma kolm_setIntegral_Iic_eq_add_intervalIntegral {g : ℝ → ℝ}
    (hg : Integrable g volume) (a u : ℝ) :
    (∫ t in Set.Iic u, g t) = (∫ t in Set.Iic a, g t) + ∫ t in a..u, g t := by
  have hdisj : ∀ x y : ℝ, Disjoint (Set.Iic x) (Set.Ioc x y) :=
    fun x y ↦ Set.disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1 h2.1
  rcases le_total a u with hau | hua
  · rw [intervalIntegral.integral_of_le hau,
      ← setIntegral_union (hdisj a u) measurableSet_Ioc hg.integrableOn hg.integrableOn,
      Iic_union_Ioc_eq_Iic hau]
  · rw [intervalIntegral.integral_of_ge hua]
    have hunion := setIntegral_union (hdisj u a) measurableSet_Ioc
      (f := g) hg.integrableOn hg.integrableOn
    rw [Iic_union_Ioc_eq_Iic hua] at hunion
    linarith

private lemma kolm_normalSteinSol_eq_neg_integral_Iic {h : ℝ → ℝ}
    (hh : Integrable h stdNormalLaw) (w : ℝ) :
    normalSteinSol h w =
      -Real.exp (w ^ 2 / 2) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t) := by
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)
  have hsum : (∫ t in Set.Iic w, g t) + (∫ t in Set.Ioi w, g t) = 0 := by
    rw [← compl_Iic, integral_add_compl measurableSet_Iic (kolm_integrable_stein_integrand hh)]
    exact kolm_integral_stein_integrand_eq_zero hh
  have hIoi : (∫ t in Set.Ioi w, g t) = -∫ t in Set.Iic w, g t := by linarith
  simp only [normalSteinSol, g] at hIoi ⊢
  rw [hIoi]
  ring

private lemma kolm_hasDerivAt_exp_half_sq (w : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (u ^ 2 / 2)) (w * Real.exp (w ^ 2 / 2)) w := by
  have h1 : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) w w := by
    convert (hasDerivAt_pow 2 w).div_const 2 using 1
    ring
  convert h1.exp using 1
  ring

private lemma kolm_hasDerivAt_exp_neg_half_sq (w : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (-u ^ 2 / 2)) (-w * Real.exp (-w ^ 2 / 2)) w := by
  have h1 : HasDerivAt (fun u : ℝ ↦ -u ^ 2 / 2) (-w) w := by
    convert (hasDerivAt_pow 2 w).fun_neg.div_const 2 using 1
    ring
  convert h1.exp using 1
  ring

private lemma kolm_exp_half_sq_mul_neg (w : ℝ) :
    Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) = 1 := by
  rw [← Real.exp_add]
  ring_nf
  exact Real.exp_zero

private lemma kolm_stein_prod_deriv_alg {h : ℝ → ℝ}
    (hh : Integrable h stdNormalLaw) (w : ℝ) :
    (-(w * Real.exp (w ^ 2 / 2)) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) +
      -Real.exp (w ^ 2 / 2) * (Real.exp (-w ^ 2 / 2) * (stdNormalExpect h - h w)) =
      w * normalSteinSol h w + h w - stdNormalExpect h := by
  set c := stdNormalExpect h
  set g := fun t ↦ Real.exp (-t ^ 2 / 2) * (c - h t)
  have hfw : normalSteinSol h w = -Real.exp (w ^ 2 / 2) * ∫ t in Set.Iic w, g t :=
    kolm_normalSteinSol_eq_neg_integral_Iic hh w
  calc
    -(w * Real.exp (w ^ 2 / 2)) * (∫ t in Set.Iic w, g t) + -Real.exp (w ^ 2 / 2) * g w
      = w * (-Real.exp (w ^ 2 / 2) * ∫ t in Set.Iic w, g t) -
          (Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2)) * (c - h w) := by
        simp only [g]
        ring
    _ = w * normalSteinSol h w + h w - c := by
        rw [← hfw, kolm_exp_half_sq_mul_neg]
        ring

private lemma kolm_continuousWithinAt_indicator_Iic (x w : ℝ) :
    ContinuousWithinAt ((Set.Iic x).indicator (1 : ℝ → ℝ)) (Set.Iic w) w := by
  rcases le_or_gt w x with hw | hw
  · refine (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ ↦ (1 : ℝ)) (Set.Iic w) w).congr (fun u hu ↦ ?_) ?_
    · have hux : u ∈ Set.Iic x := Set.mem_Iic.mpr ((Set.mem_Iic.mp hu).trans hw)
      rw [Set.indicator_of_mem hux, Pi.one_apply]
    · have hwx : w ∈ Set.Iic x := Set.mem_Iic.mpr hw
      rw [Set.indicator_of_mem hwx, Pi.one_apply]
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) w).congr
      (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hw) fun u hu ↦ ?_) |>.continuousWithinAt
    have hun : u ∉ Set.Iic x := fun h ↦ not_le_of_gt (Set.mem_Ioi.mp hu) (Set.mem_Iic.mp h)
    exact (Set.indicator_of_notMem hun _).symm

private lemma kolm_continuousAt_indicator_Iic_of_ne (x : ℝ) {w : ℝ} (hw : w ≠ x) :
    ContinuousAt ((Set.Iic x).indicator (1 : ℝ → ℝ)) w := by
  rcases lt_or_gt_of_ne hw with hlt | hgt
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) w).congr
      (Filter.eventuallyEq_of_mem (Iio_mem_nhds hlt) fun u hu ↦ ?_)
    have hux : u ∈ Set.Iic x := Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp hu))
    rw [Set.indicator_of_mem hux, Pi.one_apply]
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) w).congr
      (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hgt) fun u hu ↦ ?_)
    have hun : u ∉ Set.Iic x := fun h ↦ not_le_of_gt (Set.mem_Ioi.mp hu) (Set.mem_Iic.mp h)
    exact (Set.indicator_of_notMem hun _).symm

end Helpers

/-! ### Lemma 2.2 (Corrected): Kolmogorov Normal Stein Solution and Uniqueness -/

/-- Left-tail integral representation of the Kolmogorov Stein solution `normalSteinSolKolm x`
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:585-587`). -/
theorem normalSteinSolKolm_eq_neg_integral_Iic (x w : ℝ) :
    normalSteinSolKolm x w =
      -Real.exp (w ^ 2 / 2) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalCDF x - (Set.Iic x).indicator 1 t) := by
  rw [normalSteinSolKolm, kolm_normalSteinSol_eq_neg_integral_Iic (kolm_integrable_indicator_Iic x),
    stdNormalExpect_indicator_Iic]

/-- Uniform supremum bound $|f_x(w)| \le \sqrt{\pi / 2}$ on `normalSteinSolKolm x`
(Lemma 2.2 `\label{lem2}`, proof at `SteinIntro.tex:616-624`; Lemma 3.25 `\label{lem91}`,
`SteinIntro.tex:1677-1685`). -/
theorem abs_normalSteinSolKolm_le (x w : ℝ) :
    |normalSteinSolKolm x w| ≤ Real.sqrt (Real.pi / 2) := by
  set g : ℝ → ℝ :=
    fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalCDF x - (Set.Iic x).indicator 1 t)
  have hcdf_nn : 0 ≤ stdNormalCDF x := stdNormalCDF_nonneg x
  have hcdf_le : stdNormalCDF x ≤ 1 := stdNormalCDF_le_one x
  have hsub_le : ∀ t : ℝ, |stdNormalCDF x - (Set.Iic x).indicator 1 t| ≤ 1 := fun t ↦ by
    by_cases ht : t ∈ Set.Iic x
    · rw [Set.indicator_of_mem ht, Pi.one_apply, abs_le]
      exact ⟨by linarith, by linarith⟩
    · rw [Set.indicator_of_notMem ht, sub_zero, abs_le]
      exact ⟨by linarith, by linarith⟩
  have hg_norm : ∀ t : ℝ, ‖g t‖ ≤ Real.exp (-t ^ 2 / 2) := fun t ↦ by
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hsub_le t) (Real.exp_pos _).le).trans (by rw [mul_one])
  have hset_le : ∀ s : Set ℝ, |∫ t in s, g t| ≤ ∫ t in s, Real.exp (-t ^ 2 / 2) := fun s ↦ by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le integrable_exp_neg_sq_div_two.integrableOn
      (ae_of_all _ hg_norm)
  have hexp_nn : 0 ≤ Real.exp (w ^ 2 / 2) := (Real.exp_pos _).le
  rcases le_total 0 w with hw | hw
  · have hsol : normalSteinSolKolm x w = Real.exp (w ^ 2 / 2) * ∫ t in Set.Ioi w, g t := by
      simp only [normalSteinSolKolm, normalSteinSol, stdNormalExpect_indicator_Iic, g]
    rw [hsol, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hset_le (Set.Ioi w)) hexp_nn).trans
      (exp_mul_integral_Ioi_exp_le_sqrt_pi_div_two w hw)
  · rw [normalSteinSolKolm_eq_neg_integral_Iic x w, abs_mul, abs_neg,
      abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hset_le (Set.Iic w)) hexp_nn).trans
      (exp_mul_integral_Iic_exp_le_sqrt_pi_div_two w hw)

/-- Boundedness of the Kolmogorov Stein solution `normalSteinSolKolm x`
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`). -/
theorem bdd_normalSteinSolKolm (x : ℝ) :
    ∃ B : ℝ, ∀ w : ℝ, |normalSteinSolKolm x w| ≤ B :=
  ⟨Real.sqrt (Real.pi / 2), abs_normalSteinSolKolm_le x⟩

/-- Continuity of the Kolmogorov Stein solution `normalSteinSolKolm x` on `ℝ`
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`, `638-639`; `ISSUE-2.2`, `H3`). -/
theorem continuous_normalSteinSolKolm (x : ℝ) : Continuous (normalSteinSolKolm x) := by
  have hh := kolm_integrable_indicator_Iic x
  set g : ℝ → ℝ :=
    fun t ↦ Real.exp (-t ^ 2 / 2) *
      (stdNormalExpect ((Set.Iic x).indicator 1) - (Set.Iic x).indicator 1 t)
  have hg : Integrable g volume := kolm_integrable_stein_integrand hh
  have heq : normalSteinSolKolm x =
      fun w ↦ -Real.exp (w ^ 2 / 2) * ((∫ t in Set.Iic 0, g t) + ∫ t in (0 : ℝ)..w, g t) := by
    ext w
    rw [normalSteinSolKolm, kolm_normalSteinSol_eq_neg_integral_Iic hh w,
      kolm_setIntegral_Iic_eq_add_intervalIntegral hg 0 w]
  rw [heq]
  exact (by fun_prop : Continuous fun w : ℝ ↦ -Real.exp (w ^ 2 / 2)).mul
    (continuous_const.add (hg.continuous_primitive 0))

/-- Left-derivative Stein equation for `normalSteinSolKolm x` at every `w : ℝ`, including `w = x`
(Lemma 2.2 `\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`; `ISSUE-2.2`,
ruling `D4`). -/
theorem hasDerivWithinAt_Iic_normalSteinSolKolm (x w : ℝ) :
    HasDerivWithinAt (normalSteinSolKolm x)
      (w * normalSteinSolKolm x w + (Set.Iic x).indicator 1 w - stdNormalCDF x)
      (Set.Iic w) w := by
  set h_x : ℝ → ℝ := (Set.Iic x).indicator 1
  have hh := kolm_integrable_indicator_Iic x
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h_x - h_x t)
  have hg := kolm_integrable_stein_integrand hh
  have hgc : ContinuousWithinAt g (Set.Iic w) w :=
    (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-t ^ 2 / 2)).continuousAt
      |>.continuousWithinAt.mul
        (continuousWithinAt_const.sub (kolm_continuousWithinAt_indicator_Iic x w))
  have hI : HasDerivWithinAt (fun u ↦ ∫ t in Set.Iic u, g t) (g w) (Set.Iic w) w := by
    rw [funext (kolm_setIntegral_Iic_eq_add_intervalIntegral hg 0)]
    exact (intervalIntegral.integral_hasDerivWithinAt_right hg.intervalIntegrable
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hgc).const_add (∫ t in Set.Iic 0, g t)
  have hprod := (kolm_hasDerivAt_exp_half_sq w).fun_neg.hasDerivWithinAt.fun_mul hI
  rw [← funext (kolm_normalSteinSol_eq_neg_integral_Iic hh)] at hprod
  have hstein := hprod.congr_deriv (kolm_stein_prod_deriv_alg hh w)
  rw [stdNormalExpect_indicator_Iic] at hstein
  exact hstein

/-- Left-derivative Stein operator identity for `normalSteinSolKolm x` everywhere on `ℝ`
(Lemma 2.2 `\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`; `ISSUE-2.2`,
ruling `D4`). -/
theorem normalSteinOpLeft_normalSteinSolKolm (x w : ℝ) :
    normalSteinOpLeft (normalSteinSolKolm x) w =
      (Set.Iic x).indicator 1 w - stdNormalCDF x := by
  have hd :=
    (hasDerivWithinAt_Iic_normalSteinSolKolm x w).derivWithin (uniqueDiffWithinAt_Iic w)
  simp only [normalSteinOpLeft, hd]
  ring

/-- Two-sided derivative of `normalSteinSolKolm x` at every point `w ≠ x`
(Lemma 2.2 `\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`; `ISSUE-2.2`). -/
theorem hasDerivAt_normalSteinSolKolm_of_ne (x : ℝ) {w : ℝ} (hw : w ≠ x) :
    HasDerivAt (normalSteinSolKolm x)
      (w * normalSteinSolKolm x w + (Set.Iic x).indicator 1 w - stdNormalCDF x) w := by
  set h_x : ℝ → ℝ := (Set.Iic x).indicator 1
  have hh := kolm_integrable_indicator_Iic x
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t ^ 2 / 2) * (stdNormalExpect h_x - h_x t)
  have hg := kolm_integrable_stein_integrand hh
  have hgc : ContinuousAt g w :=
    (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-t ^ 2 / 2)).continuousAt.mul
      (continuousAt_const.sub (kolm_continuousAt_indicator_Iic_of_ne x hw))
  have hI : HasDerivAt (fun u ↦ ∫ t in Set.Iic u, g t) (g w) w := by
    rw [funext (kolm_setIntegral_Iic_eq_add_intervalIntegral hg 0)]
    exact (intervalIntegral.integral_hasDerivAt_right hg.intervalIntegrable
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hgc).const_add (∫ t in Set.Iic 0, g t)
  have hprod := (kolm_hasDerivAt_exp_half_sq w).fun_neg.fun_mul hI
  rw [← funext (kolm_normalSteinSol_eq_neg_integral_Iic hh)] at hprod
  have hstein := hprod.congr_deriv (kolm_stein_prod_deriv_alg hh w)
  rw [stdNormalExpect_indicator_Iic] at hstein
  exact hstein

private lemma eq_zero_of_bdd_continuous_hasDerivWithinAt_mul {d : ℝ → ℝ}
    (hBdd : ∃ B : ℝ, ∀ w : ℝ, |d w| ≤ B)
    (hCont : Continuous d)
    (hDeriv : ∀ w : ℝ, HasDerivWithinAt d (w * d w) (Set.Iic w) w) :
    ∀ w : ℝ, d w = 0 := by
  obtain ⟨Bd, hBd⟩ := hBdd
  let k : ℝ → ℝ := fun w ↦ Real.exp (-w ^ 2 / 2) * d w
  have hk_cont : Continuous k :=
    (by fun_prop : Continuous fun w : ℝ ↦ Real.exp (-w ^ 2 / 2)).mul hCont
  have hk_deriv : ∀ w : ℝ, HasDerivWithinAt k 0 (Set.Iic w) w := fun w ↦
    ((kolm_hasDerivAt_exp_neg_half_sq w).hasDerivWithinAt.fun_mul (hDeriv w)).congr_deriv
      (by ring)
  let m : ℝ → ℝ := fun u ↦ k (-u)
  have hm_cont : Continuous m := hk_cont.comp continuous_neg
  have hm_deriv : ∀ u : ℝ, HasDerivWithinAt m 0 (Set.Ici u) u := fun u ↦
    ((hk_deriv (-u)).comp u (hasDerivAt_neg u).hasDerivWithinAt
      (fun _ hz ↦ Set.mem_Iic.mpr (neg_le_neg (Set.mem_Ici.mp hz)))).congr_deriv (by ring)
  have hm_const : ∀ u : ℝ, m u = m 0 := fun u ↦ by
    rcases le_total 0 u with hu | hu
    · exact constant_of_has_deriv_right_zero (a := 0) (b := u) hm_cont.continuousOn
        (fun y _ ↦ hm_deriv y) u ⟨hu, le_rfl⟩
    · exact (constant_of_has_deriv_right_zero (a := u) (b := 0) hm_cont.continuousOn
        (fun y _ ↦ hm_deriv y) 0 ⟨hu, le_rfl⟩).symm
  have hk_const : ∀ w : ℝ, k w = k 0 := fun w ↦ by
    calc
      k w = m (-w) := by dsimp only [m]; rw [neg_neg]
      _ = m 0 := hm_const (-w)
      _ = k 0 := by dsimp only [m]; rw [neg_zero]
  have hk0_zero : k 0 = 0 := by
    by_contra hne
    obtain ⟨ck, hck⟩ : ∃ ck : ℝ, k 0 = ck := ⟨k 0, rfl⟩
    rw [hck] at hne
    have hpos : 0 < |ck| := abs_pos.mpr hne
    obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (|Bd| + 1) / |ck| := ⟨(|Bd| + 1) / |ck|, rfl⟩
    obtain ⟨w0, hw0_def⟩ : ∃ w0 : ℝ, w0 = max 1 (2 * |K|) := ⟨max 1 (2 * |K|), rfl⟩
    have hw0_ge1 : 1 ≤ w0 := hw0_def ▸ le_max_left _ _
    have hw0_K : 2 * |K| ≤ w0 := hw0_def ▸ le_max_right _ _
    have hrel : d w0 = ck * Real.exp (w0 ^ 2 / 2) := by
      calc
        d w0 = (Real.exp (w0 ^ 2 / 2) * Real.exp (-w0 ^ 2 / 2)) * d w0 := by
          rw [kolm_exp_half_sq_mul_neg, one_mul]
        _ = Real.exp (w0 ^ 2 / 2) * k w0 := by dsimp only [k]; ring
        _ = ck * Real.exp (w0 ^ 2 / 2) := by rw [hk_const w0, hck]; ring
    have habs_le : |ck| * Real.exp (w0 ^ 2 / 2) ≤ |Bd| := by
      have hm : |ck| * Real.exp (w0 ^ 2 / 2) = |ck * Real.exp (w0 ^ 2 / 2)| := by
        rw [abs_mul ck (Real.exp (w0 ^ 2 / 2)), abs_of_pos (Real.exp_pos _)]
      calc
        |ck| * Real.exp (w0 ^ 2 / 2) = |d w0| := by rw [hm, ← hrel]
        _ ≤ Bd := hBd w0
        _ ≤ |Bd| := le_abs_self Bd
    have hexp_ge : K ≤ Real.exp (w0 ^ 2 / 2) := by
      have hw0_nn : 0 ≤ w0 := zero_le_one.trans hw0_ge1
      have hsq : w0 ≤ w0 ^ 2 := by
        simpa only [one_mul, sq] using mul_le_mul_of_nonneg_right hw0_ge1 hw0_nn
      have hK_sq : |K| ≤ w0 ^ 2 / 2 := by linarith [hw0_K, hsq]
      linarith [le_abs_self K, Real.add_one_le_exp (w0 ^ 2 / 2)]
    have hK_eq : |ck| * K = |Bd| + 1 := by
      rw [hK_def]
      exact mul_div_cancel₀ _ hpos.ne'
    have hmul_le : |ck| * K ≤ |ck| * Real.exp (w0 ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hexp_ge hpos.le
    linarith [habs_le, hK_eq, hmul_le]
  intro w
  have hw := hk_const w
  rw [hk0_zero] at hw
  exact (mul_eq_zero.mp hw).resolve_left (Real.exp_pos _).ne'

/-- Uniqueness of the bounded continuous solution to the left-derivative Kolmogorov Stein equation
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`, `601-611`; `ISSUE-2.2`, `H3`). -/
theorem eq_normalSteinSolKolm_of_continuous_bounded (x : ℝ) {g : ℝ → ℝ}
    (hBdd : ∃ B : ℝ, ∀ w : ℝ, |g w| ≤ B)
    (hCont : Continuous g)
    (hDeriv : ∀ w : ℝ,
      HasDerivWithinAt g (w * g w + (Set.Iic x).indicator 1 w - stdNormalCDF x) (Set.Iic w) w) :
    g = normalSteinSolKolm x := by
  obtain ⟨Bg, hBg⟩ := hBdd
  have hd_bdd : ∃ B : ℝ, ∀ w : ℝ, |g w - normalSteinSolKolm x w| ≤ B :=
    ⟨Bg + Real.sqrt (Real.pi / 2), fun w ↦
      (abs_sub _ _).trans (add_le_add (hBg w) (abs_normalSteinSolKolm_le x w))⟩
  have hd_cont : Continuous (fun w ↦ g w - normalSteinSolKolm x w) :=
    hCont.sub (continuous_normalSteinSolKolm x)
  have hd_deriv : ∀ w : ℝ,
      HasDerivWithinAt (fun w ↦ g w - normalSteinSolKolm x w)
        (w * (g w - normalSteinSolKolm x w)) (Set.Iic w) w := fun w ↦ by
    refine ((hDeriv w).fun_sub (hasDerivWithinAt_Iic_normalSteinSolKolm x w)).congr_deriv ?_
    have hsub : ∀ A B C D : ℝ, (A + C - D) - (B + C - D) = A - B := fun _ _ _ _ ↦ by ring
    rw [hsub, ← mul_sub]
  ext w
  exact sub_eq_zero.mp (eq_zero_of_bdd_continuous_hasDerivWithinAt_mul hd_bdd hd_cont hd_deriv w)

/-! ### Machine-Checked Source Issue `ISSUE-2.2`: Two-Sided Derivative Non-Existence -/

/-- **Source Issue `ISSUE-2.2`** (Lemma 2.2 `\label{lem2}`, eq. `(2.1)` `\label{1a}`,
`SteinIntro.tex:578-588`): no function `f : ℝ → ℝ` satisfies the two-sided derivative ODE
`f'(w) - w f(w) = 𝕀[w ≤ x] - Φ(x)` at every `w ∈ ℝ`, by Darboux's intermediate value theorem
for derivatives across the jump at `w = x`. -/
theorem Lem2_2_twoSided_noSolution (x : ℝ) :
    ¬ ∃ f : ℝ → ℝ, ∀ w : ℝ,
      HasDerivAt f (w * f w + (Set.Iic x).indicator 1 w - stdNormalCDF x) w := by
  rintro ⟨f, hf⟩
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun w ↦ (hf w).continuousAt
  set q : ℝ → ℝ := fun w ↦ w * f w - stdNormalCDF x
  have hq_cont : Continuous q := (continuous_id.mul hf_cont).sub continuous_const
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.continuousAt_iff.mp (hq_cont.continuousAt (x := x)) (1 / 4) (by norm_num)
  set b := x + δ / 2 with hb_def
  have hab : x ≤ b := by linarith [hb_def]
  have hxb : x < b := by linarith [hb_def]
  set f' : ℝ → ℝ := fun w ↦ w * f w + (Set.Iic x).indicator 1 w - stdNormalCDF x
  have hfx : f' x = q x + 1 := by
    dsimp only [f', q]
    have hxx : x ∈ Set.Iic x := Set.mem_Iic.mpr le_rfl
    rw [Set.indicator_of_mem hxx, Pi.one_apply]
    ring
  have hbound : ∀ w : ℝ, x < w → w ≤ b → f' w < q x + 1 / 4 := by
    intro w hxw hwb
    have hdist : dist w x < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxw)]
      linarith [hb_def]
    have hq_lt : dist (q w) (q x) < 1 / 4 := hδ hdist
    rw [Real.dist_eq] at hq_lt
    have hfw : f' w = q w := by
      dsimp only [f', q]
      have hwn : w ∉ Set.Iic x := fun h ↦ not_le_of_gt hxw (Set.mem_Iic.mp h)
      rw [Set.indicator_of_notMem hwn]
      ring
    linarith [le_abs_self (q w - q x)]
  have hma : q x + 1 / 2 < f' x := by linarith
  have hmb : f' b < q x + 1 / 2 := by linarith [hbound b hxb le_rfl]
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    exists_hasDerivWithinAt_eq_of_lt_of_gt hab (fun w _ ↦ (hf w).hasDerivWithinAt) hma hmb
  linarith [hbound c hc_mem.1 hc_mem.2.le]

/-- `normalSteinSolKolm x` is not two-sided differentiable at the jump point `w = x`
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`; `ISSUE-2.2`). -/
theorem not_differentiableAt_normalSteinSolKolm (x : ℝ) :
    ¬ DifferentiableAt ℝ (normalSteinSolKolm x) x := by
  intro hd
  refine Lem2_2_twoSided_noSolution x ⟨normalSteinSolKolm x, fun w ↦ ?_⟩
  by_cases hw : w = x
  · subst hw
    have heq := (uniqueDiffWithinAt_Iic w).eq_deriv (Set.Iic w)
      hd.hasDerivAt.hasDerivWithinAt (hasDerivWithinAt_Iic_normalSteinSolKolm w w)
    exact hd.hasDerivAt.congr_deriv heq
  · exact hasDerivAt_normalSteinSolKolm_of_ne x hw

/-! ### Corollary 2.3 (Corrected) and Two-Sided Counterexample -/

/-- **Corollary 2.3 (corrected)** (`\label{cor1}`, eq. `(2.2)` `\label{1}`,
`SteinIntro.tex:591-596`; `ISSUE-2.2`, ruling `D4`): for any real-valued random variable `W`
(with no moment assumption), `|P(W ≤ x) - Φ(x)| = |E[D_- f_x(W) - W f_x(W)]|`. -/
theorem abs_measureReal_Iic_sub_stdNormalCDF_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ} (hW : AEMeasurable W P) (x : ℝ) :
    |P.real {ω | W ω ≤ x} - stdNormalCDF x| =
      |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P| := by
  set h_x : ℝ → ℝ := (Set.Iic x).indicator 1
  have hmeas_hx : Measurable h_x := measurable_one.indicator measurableSet_Iic
  have hint_hx : Integrable (fun ω ↦ h_x (W ω)) P :=
    Integrable.of_bound (hmeas_hx.comp_aemeasurable hW).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by
        by_cases hω : W ω ∈ Set.Iic x
        · dsimp only [h_x]
          rw [Set.indicator_of_mem hω, Pi.one_apply, norm_one]
        · dsimp only [h_x]
          rw [Set.indicator_of_notMem hω, norm_zero]
          exact zero_le_one)
  have hprob : P.real {ω | W ω ≤ x} = ∫ ω, h_x (W ω) ∂P := by
    have hmap : P.real {ω | W ω ≤ x} = (P.map W).real (Set.Iic x) := by
      rw [map_measureReal_apply_of_aemeasurable hW measurableSet_Iic]
      rfl
    rw [hmap, ← integral_map hW hmeas_hx.aestronglyMeasurable,
      integral_indicator_one measurableSet_Iic]
  congr 1
  rw [hprob]
  calc
    (∫ ω, h_x (W ω) ∂P) - stdNormalCDF x
      = (∫ ω, h_x (W ω) ∂P) - ∫ _ : Ω, stdNormalCDF x ∂P := by
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ = ∫ ω, (h_x (W ω) - stdNormalCDF x) ∂P :=
        (integral_sub hint_hx (integrable_const _)).symm
    _ = ∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P :=
        integral_congr_ae
          (ae_of_all _ fun ω ↦ (normalSteinOpLeft_normalSteinSolKolm x (W ω)).symm)

/-- **Source Issue `ISSUE-2.2` Counterexample** (Corollary 2.3 `\label{cor1}`,
`SteinIntro.tex:591-596`): for `W ≡ 0` on `Unit` under `Measure.dirac ()` and `x = 0`,
`|P(W ≤ 0) - Φ(0)| = 1 / 2` whereas `|E[normalSteinOp (normalSteinSolKolm 0) W]| = 0`. -/
theorem Cor2_3_twoSided_counterexample :
    |((Measure.dirac () : Measure Unit).real {ω : Unit | (fun _ : Unit ↦ (0 : ℝ)) ω ≤ 0}) -
      stdNormalCDF 0| ≠
    |∫ ω : Unit, normalSteinOp (normalSteinSolKolm 0) ((fun _ : Unit ↦ (0 : ℝ)) ω)
      ∂(Measure.dirac ())| := by
  have hlhs_prob :
      (Measure.dirac () : Measure Unit).real {ω : Unit | (fun _ : Unit ↦ (0 : ℝ)) ω ≤ 0} = 1 :=
    Measure.dirac_real_apply_of_mem (le_rfl : (0 : ℝ) ≤ 0)
  have hlhs :
      |((Measure.dirac () : Measure Unit).real {ω : Unit | (fun _ : Unit ↦ (0 : ℝ)) ω ≤ 0}) -
        stdNormalCDF 0| = 1 / 2 := by
    rw [hlhs_prob, stdNormalCDF_zero]
    norm_num
  have hOp0 : normalSteinOp (normalSteinSolKolm 0) 0 = 0 := by
    simp only [normalSteinOp,
      deriv_zero_of_not_differentiableAt (not_differentiableAt_normalSteinSolKolm 0),
      zero_mul, sub_zero]
  have hrhs :
      |∫ ω : Unit, normalSteinOp (normalSteinSolKolm 0) ((fun _ : Unit ↦ (0 : ℝ)) ω)
        ∂(Measure.dirac ())| = 0 := by
    simp only [hOp0, integral_zero, abs_zero]
  rw [hlhs, hrhs]
  norm_num

/-! ### Proposition 2.4: General Integral Probability Metric Identity -/

/-- **Proposition 2.4** (`\label{prop31}`, eq. `(2.5)` `\label{31}`, `SteinIntro.tex:665-670`;
rulings `D1`, `D4`): for any real-valued random variable `W`, any `Z` with standard normal law,
any test class `H : Set (ℝ → ℝ)`, and any family `f : (ℝ → ℝ) → ℝ → ℝ` solving the two-sided
normal Stein equation `f_h'(w) - w f_h(w) = h(w) - Φ(h)` for all `h ∈ H`, the integral
probability metric `ipm H (P.map W) (P'.map Z)` equals the `ℝ≥0∞` supremum of
`ENNReal.ofReal |∫ ω, normalSteinOp (f h) (W ω) ∂P|` over integrable `h ∈ H`. -/
theorem ipm_map_stdNormalLaw_eq_iSup_normalSteinOp {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (hW : AEMeasurable W P) (hZ_law : P'.map Z = stdNormalLaw)
    (H : Set (ℝ → ℝ)) (f : (ℝ → ℝ) → ℝ → ℝ)
    (hf : ∀ h ∈ H, ∀ w : ℝ, HasDerivAt (f h) (w * f h w + h w - stdNormalExpect h) w) :
    ipm H (P.map W) (P'.map Z) =
      ⨆ h ∈ H, ⨆ (_ : Integrable h (P.map W) ∧ Integrable h (P'.map Z)),
        ENNReal.ofReal |∫ ω, normalSteinOp (f h) (W ω) ∂P| := by
  unfold ipm
  refine iSup_congr fun h ↦ iSup_congr fun hh ↦ iSup_congr fun hInt ↦ ?_
  have hOp : ∀ w : ℝ, normalSteinOp (f h) w = h w - stdNormalExpect h := fun w ↦ by
    have hd := (hf h hh w).deriv
    simp only [normalSteinOp, hd]
    ring
  have hInt_comp : Integrable (fun ω ↦ h (W ω)) P :=
    (integrable_map_measure hInt.1.aestronglyMeasurable hW).mp hInt.1
  have hLHS : (∫ x, h x ∂(P.map W)) - (∫ z, h z ∂(P'.map Z)) =
      ∫ ω, normalSteinOp (f h) (W ω) ∂P := by
    rw [integral_map hW hInt.1.aestronglyMeasurable, hZ_law]
    change (∫ ω, h (W ω) ∂P) - stdNormalExpect h = ∫ ω, normalSteinOp (f h) (W ω) ∂P
    calc
      (∫ ω, h (W ω) ∂P) - stdNormalExpect h
        = (∫ ω, h (W ω) ∂P) - ∫ _ : Ω, stdNormalExpect h ∂P := by
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ = ∫ ω, (h (W ω) - stdNormalExpect h) ∂P :=
          (integral_sub hInt_comp (integrable_const _)).symm
      _ = ∫ ω, normalSteinOp (f h) (W ω) ∂P :=
          integral_congr_ae (ae_of_all _ fun ω ↦ (hOp (W ω)).symm)
  rw [hLHS]

end SteinMethod
