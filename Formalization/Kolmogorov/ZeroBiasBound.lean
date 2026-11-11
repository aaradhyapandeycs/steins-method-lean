/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Couplings
import Formalization.Kolmogorov.SolutionBounds

/-!
# Zero-Bias Kolmogorov Normal Approximation Bound (`Formalization.Kolmogorov.ZeroBiasBound`)

Proves Section 3.6.1 of Nathan Ross, *"Fundamentals of Stein's method"* (`Probability Surveys` 8,
2011; `arXiv:1109.1880v1`, `SteinIntro.tex:1695-1744`):

* `kolmogorovDist_le_add_of_ae_abs_sub_le` & `abs_kolmogorovDist_toReal_sub_le_of_ae_abs_sub_le`
  (eqs. `(3.39)`–`(3.40)` `\label{93}`–`\label{94}`, `SteinIntro.tex:1712-1728`):
  $|d_{\mathrm{K}}(W, Z) - d_{\mathrm{K}}(W^z, Z)| \le \delta / \sqrt{2\pi}$ when
  $|W^z - W| \le \delta$ almost surely.
* `abs_integral_normalSteinOp_le_of_isZeroBias_bdd` (eq. `(3.42)` `\label{95}`,
  `SteinIntro.tex:1734-1738`): $|\mathbb{E}[f'(W^z) - W^z f(W^z)]| \le \delta(1 + \sqrt{2\pi}/4)$
  for $f \in \mathrm{normalKolmogorovClass}$.
* `kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd` (**Theorem 3.27**, `SteinIntro.tex:1697-1704`;
  `ISSUE-3.10`, `D9`):
  $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  (1 + 1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,\delta$.
* `ae_abs_le_of_isZeroBias_of_ae_abs_le` (`Sec3_6_zeroBias_bdd_restricted`,
  `SteinIntro.tex:1741-1742`): if $\operatorname{Var}(W) > 0$ and $|W| \le M$ a.s., then every
  zero-bias version $W^z$ satisfies $|W^z| \le M$ a.s., together with the
  $\operatorname{Var}(W) = 0$ counterexample `zero_stdNormalLaw_isZeroBias_unbounded` and the
  existence-reading reduction `exists_bdd_zeroBias_of_pos_var_exists`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: First-Moment Bound and Coupled Kolmogorov Shift Inequality -/

/-- If $W \in L^2(P)$ has mean zero and unit variance on a probability space, then
$\mathbb{E}|W| \le 1$ (used in Theorem 3.27, `SteinIntro.tex:1737`, and Theorem 3.28 / Lemma 3.29,
`SteinIntro.tex:1778, 1802`). -/
theorem integral_abs_le_one_of_integral_eq_zero_of_variance_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW : MemLp W 2 P) (hmean : ∫ ω, W ω ∂P = 0)
    (hvar : ProbabilityTheory.variance W P = 1) :
    ∫ ω, |W ω| ∂P ≤ 1 := by
  have hsq : ∫ ω, W ω ^ 2 ∂P = 1 := by
    rw [← ProbabilityTheory.variance_of_integral_eq_zero hW.aemeasurable hmean, hvar]
  have hint_abs : Integrable (fun ω ↦ |W ω|) P := (hW.integrable one_le_two).norm
  have hint_sq : Integrable (fun ω ↦ W ω ^ 2) P := hW.integrable_sq
  have hpt : ∀ ω : Ω, 2 * |W ω| ≤ W ω ^ 2 + 1 := fun ω ↦ by
    nlinarith [sq_nonneg (|W ω| - 1), sq_abs (W ω)]
  have hint_le : ∫ ω, (2 * |W ω|) ∂P ≤ ∫ ω, (W ω ^ 2 + 1) ∂P :=
    integral_mono (hint_abs.const_mul 2) (hint_sq.add (integrable_const 1)) hpt
  rw [integral_const_mul, integral_add hint_sq (integrable_const 1), hsq, integral_const,
    probReal_univ, smul_eq_mul, one_mul] at hint_le
  linarith

private lemma nonneg_of_ae_abs_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} {δ : ℝ} (hδ : ∀ᵐ ω ∂P, |X ω| ≤ δ) : 0 ≤ δ := by
  have : (ae P).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω, hω⟩ := hδ.exists
  exact (abs_nonneg _).trans hω

private lemma measureReal_le_of_ae_imp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {A B : Set Ω} (hAB : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B) :
    P.real A ≤ P.real B := by
  have hnull : P {ω | ¬ (ω ∈ A → ω ∈ B)} = 0 := ae_iff.mp hAB
  have hsub : A ⊆ B ∪ {ω | ¬ (ω ∈ A → ω ∈ B)} := fun ω hAω ↦ by
    by_cases hBω : ω ∈ B
    · exact Or.inl hBω
    · exact Or.inr fun h ↦ hBω (h hAω)
  have hle : P A ≤ P B := by
    calc P A ≤ P (B ∪ {ω | ¬ (ω ∈ A → ω ∈ B)}) := measure_mono hsub
      _ ≤ P B + P {ω | ¬ (ω ∈ A → ω ∈ B)} := measure_union_le _ _
      _ = P B := by rw [hnull, add_zero]
  exact ENNReal.toReal_mono (measure_ne_top P B) hle

/-- Coupled Kolmogorov triangle inequality against $\mathcal{N}(0, 1)$
(eq. `(3.39)` `\label{93}`, `SteinIntro.tex:1712-1725`): if $|W^z - W| \le \delta$ a.s., then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
d_{\mathrm{K}}(\mathcal{L}(W^z), \mathcal{L}(Z)) + \delta / \sqrt{2\pi}$. -/
theorem kolmogorovDist_le_add_of_ae_abs_sub_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ} {δ : ℝ}
    (hW : AEMeasurable W P) (hWz : AEMeasurable Wz P)
    (_hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw)
    (hδ : ∀ᵐ ω ∂P, |Wz ω - W ω| ≤ δ) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      kolmogorovDist (P.map Wz) (P'.map Z) +
        ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) := by
  have hδ_nn : 0 ≤ δ := nonneg_of_ae_abs_le P hδ
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have : IsProbabilityMeasure (P.map Wz) := (Measure.isProbabilityMeasure_map_iff hWz).mpr ‹_›
  rw [hZ_law, kolmogorovDist_eq_iSup (P.map W) stdNormalLaw,
    kolmogorovDist_eq_iSup (P.map Wz) stdNormalLaw]
  set K := ⨆ x : ℝ, ENNReal.ofReal |(P.map Wz).real (Iic x) - stdNormalLaw.real (Iic x)|
  refine iSup_le fun z ↦ ?_
  have hmapW : ∀ y : ℝ, (P.map W).real (Iic y) = P.real {ω | W ω ≤ y} := fun y ↦
    map_measureReal_apply_of_aemeasurable hW measurableSet_Iic
  have hmapWz : ∀ y : ℝ, (P.map Wz).real (Iic y) = P.real {ω | Wz ω ≤ y} := fun y ↦
    map_measureReal_apply_of_aemeasurable hWz measurableSet_Iic
  have hmapZ : ∀ y : ℝ, stdNormalLaw.real (Iic y) = stdNormalCDF y := fun y ↦
    (cdf_eq_real stdNormalLaw y).symm
  rw [hmapW z, hmapZ z]
  have hP_up : P.real {ω | W ω ≤ z} ≤ P.real {ω | Wz ω ≤ z + δ} := by
    refine measureReal_le_of_ae_imp P ?_
    filter_upwards [hδ] with ω hω hWz_le
    linarith [(abs_le.mp hω).2]
  have hP_lo : P.real {ω | Wz ω ≤ z - δ} ≤ P.real {ω | W ω ≤ z} := by
    refine measureReal_le_of_ae_imp P ?_
    filter_upwards [hδ] with ω hω hWz_le
    linarith [(abs_le.mp hω).1]
  have hZ_up : stdNormalCDF (z + δ) - stdNormalCDF z ≤ δ / Real.sqrt (2 * Real.pi) := by
    have h := abs_stdNormalCDF_sub_le z (z + δ)
    have heq : |(z + δ) - z| = δ := by rw [add_sub_cancel_left, abs_of_nonneg hδ_nn]
    rw [heq] at h
    exact (le_abs_self _).trans h
  have hZ_lo : stdNormalCDF z - stdNormalCDF (z - δ) ≤ δ / Real.sqrt (2 * Real.pi) := by
    have h := abs_stdNormalCDF_sub_le (z - δ) z
    have heq : |z - (z - δ)| = δ := by rw [sub_sub_cancel, abs_of_nonneg hδ_nn]
    rw [heq] at h
    exact (le_abs_self _).trans h
  rcases le_total 0 (P.real {ω | W ω ≤ z} - stdNormalCDF z) with hsign | hsign
  · rw [abs_of_nonneg hsign]
    have hle : P.real {ω | W ω ≤ z} - stdNormalCDF z ≤
        |(P.map Wz).real (Iic (z + δ)) - stdNormalLaw.real (Iic (z + δ))| +
          δ / Real.sqrt (2 * Real.pi) := by
      rw [hmapWz (z + δ), hmapZ (z + δ)]
      linarith [le_abs_self (P.real {ω | Wz ω ≤ z + δ} - stdNormalCDF (z + δ))]
    calc ENNReal.ofReal (P.real {ω | W ω ≤ z} - stdNormalCDF z)
        ≤ ENNReal.ofReal
            (|(P.map Wz).real (Iic (z + δ)) - stdNormalLaw.real (Iic (z + δ))| +
              δ / Real.sqrt (2 * Real.pi)) := ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal |(P.map Wz).real (Iic (z + δ)) - stdNormalLaw.real (Iic (z + δ))| +
            ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) :=
          ENNReal.ofReal_add (abs_nonneg _) (by positivity)
      _ ≤ K + ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) := by
          gcongr
          exact le_iSup (fun x : ℝ ↦ ENNReal.ofReal |(P.map Wz).real (Iic x) -
            stdNormalLaw.real (Iic x)|) (z + δ)
  · have habs : |P.real {ω | W ω ≤ z} - stdNormalCDF z| =
        stdNormalCDF z - P.real {ω | W ω ≤ z} := by
      rw [abs_of_nonpos hsign]; ring
    rw [habs]
    have hle : stdNormalCDF z - P.real {ω | W ω ≤ z} ≤
        |(P.map Wz).real (Iic (z - δ)) - stdNormalLaw.real (Iic (z - δ))| +
          δ / Real.sqrt (2 * Real.pi) := by
      rw [hmapWz (z - δ), hmapZ (z - δ)]
      linarith [neg_le_abs (P.real {ω | Wz ω ≤ z - δ} - stdNormalCDF (z - δ))]
    calc ENNReal.ofReal (stdNormalCDF z - P.real {ω | W ω ≤ z})
        ≤ ENNReal.ofReal
            (|(P.map Wz).real (Iic (z - δ)) - stdNormalLaw.real (Iic (z - δ))| +
              δ / Real.sqrt (2 * Real.pi)) := ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal |(P.map Wz).real (Iic (z - δ)) - stdNormalLaw.real (Iic (z - δ))| +
            ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) :=
          ENNReal.ofReal_add (abs_nonneg _) (by positivity)
      _ ≤ K + ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) := by
          gcongr
          exact le_iSup (fun x : ℝ ↦ ENNReal.ofReal |(P.map Wz).real (Iic x) -
            stdNormalLaw.real (Iic x)|) (z - δ)

private lemma kolmogorovDist_le_one_of_prob (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kolmogorovDist μ ν ≤ 1 := by
  rw [kolmogorovDist_eq_iSup]
  refine iSup_le fun x ↦ ?_
  rw [ENNReal.ofReal_le_one, abs_le]
  have hμ0 : 0 ≤ μ.real (Iic x) := measureReal_nonneg
  have hμ1 : μ.real (Iic x) ≤ 1 := by
    simp only [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hν0 : 0 ≤ ν.real (Iic x) := measureReal_nonneg
  have hν1 : ν.real (Iic x) ≤ 1 := by
    simp only [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  exact ⟨by linarith, by linarith⟩

/-- Proof display `(3.40)` (`\label{94}`, `SteinIntro.tex:1726-1728`): if $|W^z - W| \le \delta$
a.s., then $|d_{\mathrm{K}}(W, Z) - d_{\mathrm{K}}(W^z, Z)| \le \delta / \sqrt{2\pi}$. -/
theorem abs_kolmogorovDist_toReal_sub_le_of_ae_abs_sub_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ} {δ : ℝ}
    (hW : AEMeasurable W P) (hWz : AEMeasurable Wz P)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw)
    (hδ : ∀ᵐ ω ∂P, |Wz ω - W ω| ≤ δ) :
    |(kolmogorovDist (P.map W) (P'.map Z)).toReal -
        (kolmogorovDist (P.map Wz) (P'.map Z)).toReal| ≤
      δ / Real.sqrt (2 * Real.pi) := by
  have hδ_nn : 0 ≤ δ := nonneg_of_ae_abs_le P hδ
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have : IsProbabilityMeasure (P.map Wz) := (Measure.isProbabilityMeasure_map_iff hWz).mpr ‹_›
  have : IsProbabilityMeasure (P'.map Z) := (Measure.isProbabilityMeasure_map_iff hZ).mpr ‹_›
  have hfin1 : kolmogorovDist (P.map W) (P'.map Z) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (kolmogorovDist_le_one_of_prob _ _)
  have hfin2 : kolmogorovDist (P.map Wz) (P'.map Z) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (kolmogorovDist_le_one_of_prob _ _)
  have h1 := kolmogorovDist_le_add_of_ae_abs_sub_le P P' hW hWz hZ hZ_law hδ
  have hδ_symm : ∀ᵐ ω ∂P, |W ω - Wz ω| ≤ δ := by
    filter_upwards [hδ] with ω hω
    rwa [abs_sub_comm]
  have h2 := kolmogorovDist_le_add_of_ae_abs_sub_le P P' hWz hW hZ hZ_law hδ_symm
  have hr1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin2, ENNReal.ofReal_ne_top⟩) h1
  have hr2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, ENNReal.ofReal_ne_top⟩) h2
  rw [ENNReal.toReal_add hfin2 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)] at hr1
  rw [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)] at hr2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### Section 2: Zero-Bias Stein Bound and Theorem 3.27 (`Thm3_27`) -/

/-- Proof display `(3.42)` (`\label{95}`, `SteinIntro.tex:1734-1738`): for mean-zero,
unit-variance $W$ and zero-bias $W^z$ on the same space with $|W^z - W| \le \delta$ a.s., every
$f \in \mathrm{normalKolmogorovClass}$ satisfies
$|\mathbb{E}[f'(W^z) - W^z f(W^z)]| \le (1 + \sqrt{2\pi}/4)\,\delta$. -/
theorem abs_integral_normalSteinOp_le_of_isZeroBias_bdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W Wz : Ω → ℝ} {δ : ℝ} {f : ℝ → ℝ}
    (hvar : ProbabilityTheory.variance W P = 1)
    (hWz : IsZeroBias P W P Wz)
    (hδ : ∀ᵐ ω ∂P, |Wz ω - W ω| ≤ δ)
    (hf : f ∈ normalKolmogorovClass) :
    |∫ ω, normalSteinOp f (Wz ω) ∂P| ≤ (1 + Real.sqrt (2 * Real.pi) / 4) * δ := by
  have hδ_nn : 0 ≤ δ := nonneg_of_ae_abs_le P hδ
  have hW_int : Integrable W P := hWz.1.integrable one_le_two
  have hdiff_int : Integrable (fun ω ↦ Wz ω - W ω) P :=
    Integrable.of_bound (hWz.2.2.1.sub hWz.1.aemeasurable).aestronglyMeasurable δ
      (by filter_upwards [hδ] with ω hω; rwa [Real.norm_eq_abs])
  have hWz_int : Integrable Wz P := by
    refine (hdiff_int.add hW_int).congr (ae_of_all _ fun ω ↦ ?_)
    simp only [Pi.add_apply]; ring
  have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_of_mem_normalKolmogorovClass hf
  have hWf_int : Integrable (fun ω ↦ W ω * f (W ω)) P :=
    integrable_mul_comp_of_mem_normalKolmogorovClass hW_int hf
  have hWzf_int : Integrable (fun ω ↦ Wz ω * f (Wz ω)) P :=
    integrable_mul_comp_of_mem_normalKolmogorovClass hWz_int hf
  have hderiv_int : Integrable (fun ω ↦ deriv f (Wz ω)) P :=
    integrable_deriv_comp_of_mem_normalKolmogorovClass hWz.2.2.1 hf
  have hzb := hWz.2.2.2 f hf_ac hWf_int hderiv_int
  rw [hvar, one_mul] at hzb
  have hstein_eq : ∫ ω, normalSteinOp f (Wz ω) ∂P =
      ∫ ω, (W ω * f (W ω) - Wz ω * f (Wz ω)) ∂P := by
    unfold normalSteinOp
    rw [integral_sub hderiv_int hWzf_int, ← hzb, ← integral_sub hWf_int hWzf_int]
  rw [hstein_eq, ← Real.norm_eq_abs]
  have hW_abs_int : Integrable (fun ω ↦ |W ω|) P := by
    simpa only [Real.norm_eq_abs] using hW_int.norm
  have hrhs_int : Integrable (fun ω ↦ (|W ω| + Real.sqrt (2 * Real.pi) / 4) * δ) P :=
    (hW_abs_int.add (integrable_const _)).mul_const δ
  have hpt : ∀ᵐ ω ∂P, ‖W ω * f (W ω) - Wz ω * f (Wz ω)‖ ≤
      (|W ω| + Real.sqrt (2 * Real.pi) / 4) * δ := by
    filter_upwards [hδ] with ω hω
    rw [Real.norm_eq_abs]
    have h3 := hf.2.2.2 0 (Wz ω - W ω) (W ω)
    have hsimp : (W ω + 0) * f (W ω + 0) - (W ω + (Wz ω - W ω)) * f (W ω + (Wz ω - W ω)) =
        W ω * f (W ω) - Wz ω * f (Wz ω) := by
      have hw : W ω + (Wz ω - W ω) = Wz ω := by ring
      rw [add_zero, hw]
    rw [hsimp, abs_zero, zero_add] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left hω (by positivity))
  have hint_le := norm_integral_le_of_norm_le hrhs_int hpt
  have hrhs_eval : ∫ ω, (|W ω| + Real.sqrt (2 * Real.pi) / 4) * δ ∂P ≤
      (1 + Real.sqrt (2 * Real.pi) / 4) * δ := by
    rw [integral_mul_const, integral_add hW_abs_int (integrable_const _), integral_const,
      probReal_univ, smul_eq_mul, one_mul]
    have hW1 := integral_abs_le_one_of_integral_eq_zero_of_variance_eq_one P hWz.1 hWz.2.1 hvar
    exact mul_le_mul_of_nonneg_right (by linarith) hδ_nn
  exact hint_le.trans hrhs_eval

/-- **Theorem 3.27** (`SteinIntro.tex:1697-1704`, §3.6.1; `ISSUE-3.10`, ruling `D9`): if $W$ has
mean zero and variance one, $W^z$ has the zero-bias distribution of $W$ on the same probability
space with $|W^z - W| \le \delta$ almost surely, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
(1 + 1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,\delta$. -/
theorem kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ} {δ : ℝ}
    (hvar : ProbabilityTheory.variance W P = 1)
    (hWz : IsZeroBias P W P Wz)
    (hδ : ∀ᵐ ω ∂P, |Wz ω - W ω| ≤ δ)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * δ) := by
  have hδ_nn : 0 ≤ δ := nonneg_of_ae_abs_le P hδ
  have hW_int : Integrable W P := hWz.1.integrable one_le_two
  have hdiff_int : Integrable (fun ω ↦ Wz ω - W ω) P :=
    Integrable.of_bound (hWz.2.2.1.sub hWz.1.aemeasurable).aestronglyMeasurable δ
      (by filter_upwards [hδ] with ω hω; rwa [Real.norm_eq_abs])
  have hWz_int : Integrable Wz P := by
    refine (hdiff_int.add hW_int).congr (ae_of_all _ fun ω ↦ ?_)
    simp only [Pi.add_apply]; ring
  have hstep1 := kolmogorovDist_le_add_of_ae_abs_sub_le P P' hWz.1.aemeasurable hWz.2.2.1 hZ
    hZ_law hδ
  have hstep2 := kolmogorovDist_map_stdNormal_le_iSup_normalSteinOp P P' hWz_int hZ hZ_law
  have hstep3 : (⨆ f ∈ normalKolmogorovClass, ENNReal.ofReal |∫ ω, normalSteinOp f (Wz ω) ∂P|) ≤
      ENNReal.ofReal ((1 + Real.sqrt (2 * Real.pi) / 4) * δ) := by
    refine iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_
    exact abs_integral_normalSteinOp_le_of_isZeroBias_bdd P hvar hWz hδ hf
  have hcomb : ENNReal.ofReal ((1 + Real.sqrt (2 * Real.pi) / 4) * δ) +
      ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) =
      ENNReal.ofReal ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * δ) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc kolmogorovDist (P.map W) (P'.map Z)
      ≤ kolmogorovDist (P.map Wz) (P'.map Z) + ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) :=
        hstep1
    _ ≤ (⨆ f ∈ normalKolmogorovClass, ENNReal.ofReal |∫ ω, normalSteinOp f (Wz ω) ∂P|) +
          ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) := by gcongr
    _ ≤ ENNReal.ofReal ((1 + Real.sqrt (2 * Real.pi) / 4) * δ) +
          ENNReal.ofReal (δ / Real.sqrt (2 * Real.pi)) := by gcongr
    _ = ENNReal.ofReal ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * δ) :=
        hcomb

/-! ### Section 3: Boundedness Inheritance of Zero-Bias (`SteinIntro.tex:1741-1742`, B2) -/

private def extCutoff (M t : ℝ) : ℝ :=
  min 1 (max 0 (t - M)) + min 1 (max 0 (-t - M))

private lemma continuous_extCutoff (M : ℝ) : Continuous (extCutoff M) := by
  unfold extCutoff
  fun_prop

private lemma extCutoff_bounds {M : ℝ} (_ : 0 ≤ M) (t : ℝ) :
    0 ≤ extCutoff M t ∧ extCutoff M t ≤ 1 := by
  unfold extCutoff
  have hnn1 : 0 ≤ min (1 : ℝ) (max 0 (t - M)) := le_min zero_le_one (le_max_left 0 _)
  have hnn2 : 0 ≤ min (1 : ℝ) (max 0 (-t - M)) := le_min zero_le_one (le_max_left 0 _)
  refine ⟨by linarith, ?_⟩
  rcases le_total 0 t with ht | ht
  · have hzero : min (1 : ℝ) (max 0 (-t - M)) = 0 := by
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]
    rw [hzero, add_zero]
    exact min_le_left 1 _
  · have hzero : min (1 : ℝ) (max 0 (t - M)) = 0 := by
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]
    rw [hzero, zero_add]
    exact min_le_left 1 _

private lemma extCutoff_eq_zero_iff (M t : ℝ) :
    extCutoff M t = 0 ↔ |t| ≤ M := by
  unfold extCutoff
  have hnn1 : 0 ≤ min (1 : ℝ) (max 0 (t - M)) := le_min zero_le_one (le_max_left 0 _)
  have hnn2 : 0 ≤ min (1 : ℝ) (max 0 (-t - M)) := le_min zero_le_one (le_max_left 0 _)
  constructor
  · intro hsum
    have h1 : min (1 : ℝ) (max 0 (t - M)) = 0 := by linarith
    have h2 : min (1 : ℝ) (max 0 (-t - M)) = 0 := by linarith
    have ht1 : t ≤ M := by
      by_contra hgt
      push Not at hgt
      have hpos : 0 < min (1 : ℝ) (max 0 (t - M)) :=
        lt_min zero_lt_one (lt_of_lt_of_le (by linarith) (le_max_right 0 _))
      linarith
    have ht2 : -M ≤ t := by
      by_contra hlt
      push Not at hlt
      have hpos : 0 < min (1 : ℝ) (max 0 (-t - M)) :=
        lt_min zero_lt_one (lt_of_lt_of_le (by linarith) (le_max_right 0 _))
      linarith
    exact abs_le.mpr ⟨ht2, ht1⟩
  · intro habs
    obtain ⟨ht1, ht2⟩ := abs_le.mp habs
    have h1 : max (0 : ℝ) (t - M) = 0 := max_eq_left (by linarith)
    have h2 : max (0 : ℝ) (-t - M) = 0 := max_eq_left (by linarith)
    rw [h1, h2, min_eq_right zero_le_one, add_zero]

/-- **Section 3.6.1 Boundedness Inheritance (restricted to $\operatorname{Var}(W) > 0$)**
(`Sec3_6_zeroBias_bdd_restricted`, `SteinIntro.tex:1741-1742`; `ISSUE-3.19`): if
$\operatorname{Var}(W) > 0$, $|W| \le M$ almost surely, and $W^z$ has the zero-bias distribution of
$W$ on $(Ω', P')$, then $|W^z| \le M$ almost surely under $P'$. -/
theorem ae_abs_le_of_isZeroBias_of_ae_abs_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Wz : Ω' → ℝ} {M : ℝ}
    (hvar : 0 < ProbabilityTheory.variance W P)
    (hWz : IsZeroBias P W P' Wz)
    (hbdd : ∀ᵐ ω ∂P, |W ω| ≤ M) :
    ∀ᵐ ω' ∂P', |Wz ω'| ≤ M := by
  have hM : 0 ≤ M := nonneg_of_ae_abs_le P hbdd
  set ψ : ℝ → ℝ := extCutoff M
  have hψ_cont : Continuous ψ := continuous_extCutoff M
  set f : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, ψ t
  have hf_deriv : ∀ x : ℝ, HasDerivAt f (ψ x) x := fun x ↦
    intervalIntegral.integral_hasDerivAt_right (hψ_cont.intervalIntegrable 0 x)
      (hψ_cont.stronglyMeasurableAtFilter volume (𝓝 x)) hψ_cont.continuousAt
  have hf_diff : Differentiable ℝ f := fun x ↦ (hf_deriv x).differentiableAt
  have hf_lip : LipschitzWith 1 f := by
    refine lipschitzWith_of_nnnorm_deriv_le hf_diff fun x ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, (hf_deriv x).deriv,
      abs_of_nonneg (extCutoff_bounds hM x).1, NNReal.coe_one]
    exact (extCutoff_bounds hM x).2
  have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b := fun a b ↦
    hf_lip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hf_zero_on_Icc : ∀ x : ℝ, |x| ≤ M → f x = 0 := by
    intro x hx
    have hcongr : ∫ t in (0 : ℝ)..x, ψ t = ∫ _ in (0 : ℝ)..x, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [extCutoff_eq_zero_iff M]
      obtain ⟨ht1, ht2⟩ := Set.mem_Icc.mp ht
      obtain ⟨hx1, hx2⟩ := abs_le.mp hx
      refine abs_le.mpr ⟨?_, ?_⟩
      · have hmin : -M ≤ min (0 : ℝ) x := le_min (by linarith) hx1
        linarith
      · have hmax : max (0 : ℝ) x ≤ M := max_le hM hx2
        linarith
    simp [f, hcongr]
  have hWf_ae_zero : (fun ω ↦ W ω * f (W ω)) =ᵐ[P] 0 := by
    filter_upwards [hbdd] with ω hω
    simp [hf_zero_on_Icc (W ω) hω]
  have hWf_int : Integrable (fun ω ↦ W ω * f (W ω)) P :=
    (integrable_zero _ _ _).congr hWf_ae_zero.symm
  have hderiv_eq : ∀ u : ℝ, deriv f u = ψ u := fun u ↦ (hf_deriv u).deriv
  have hderiv_int : Integrable (fun ω' ↦ deriv f (Wz ω')) P' := by
    refine Integrable.of_bound
      ((hψ_cont.measurable.comp_aemeasurable hWz.2.2.1).aestronglyMeasurable.congr
        (ae_of_all _ fun ω' ↦ (hderiv_eq (Wz ω')).symm)) 1 ?_
    exact ae_of_all _ fun ω' ↦ by
      rw [Real.norm_eq_abs, hderiv_eq, abs_of_nonneg (extCutoff_bounds hM (Wz ω')).1]
      exact (extCutoff_bounds hM (Wz ω')).2
  have hzb := hWz.2.2.2 f hf_ac hWf_int hderiv_int
  have hlhs_zero : ∫ ω, W ω * f (W ω) ∂P = 0 := by
    rw [integral_congr_ae hWf_ae_zero]
    simp
  rw [hlhs_zero] at hzb
  have hint_ψ_zero : ∫ ω', ψ (Wz ω') ∂P' = 0 := by
    have hmul_zero : ProbabilityTheory.variance W P * ∫ ω', deriv f (Wz ω') ∂P' = 0 := hzb.symm
    have hd_zero : ∫ ω', deriv f (Wz ω') ∂P' = 0 :=
      (mul_eq_zero.mp hmul_zero).resolve_left hvar.ne'
    simpa only [hderiv_eq] using hd_zero
  have hψ_int : Integrable (fun ω' ↦ ψ (Wz ω')) P' := by
    simpa only [hderiv_eq] using hderiv_int
  have hψ_ae_zero : (fun ω' ↦ ψ (Wz ω')) =ᵐ[P'] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω' ↦ (extCutoff_bounds hM (Wz ω')).1) hψ_int).mp
      hint_ψ_zero
  filter_upwards [hψ_ae_zero] with ω' hω'
  exact (extCutoff_eq_zero_iff M (Wz ω')).mp hω'

/-- **Counterexample at $\operatorname{Var}(W) = 0$** (`SteinIntro.tex:1741-1742`, `ISSUE-3.19`):
for $W \equiv 0$ on `(Unit, dirac ())`, $W^z \sim \mathcal{N}(0, 1)$ satisfies
`IsZeroBias (Measure.dirac ()) (fun _ ↦ 0) stdNormalLaw id` while $|W| \le 0$ everywhere and $W^z$
is not almost surely bounded by any $M \in \mathbb{R}$. -/
theorem zero_stdNormalLaw_isZeroBias_unbounded :
    let P : Measure Unit := Measure.dirac ()
    let W : Unit → ℝ := fun _ ↦ 0
    IsZeroBias P W stdNormalLaw id ∧
      (∀ᵐ ω ∂P, |W ω| ≤ 0) ∧
      ¬ ∃ M : ℝ, ∀ᵐ x : ℝ ∂stdNormalLaw, |x| ≤ M := by
  refine ⟨⟨memLp_const 0, by simp, aemeasurable_id, fun f _ _ _ ↦ ?_⟩,
    ae_of_all _ (fun _ ↦ by simp), ?_⟩
  · have hvar0 : ProbabilityTheory.variance (fun _ : Unit ↦ (0 : ℝ)) (Measure.dirac ()) = 0 :=
      ProbabilityTheory.variance_zero _
    simp [hvar0]
  · rintro ⟨M, hM⟩
    set B : ℝ := max 0 M
    have hIic : ∀ᵐ x : ℝ ∂stdNormalLaw, x ∈ Iic B := by
      filter_upwards [hM] with x hx
      exact mem_Iic.mpr ((le_abs_self x).trans (hx.trans (le_max_right 0 M)))
    have hcompl : stdNormalLaw (Iic B)ᶜ = 0 := ae_iff.mp hIic
    have huniv : stdNormalLaw (Iic B) = 1 := by
      have hadd := prob_add_prob_compl (μ := stdNormalLaw) measurableSet_Iic (s := Iic B)
      rwa [hcompl, add_zero] at hadd
    have hcdf1 : stdNormalCDF B = 1 := by
      have hmapZ : stdNormalLaw.real (Iic B) = stdNormalCDF B := (cdf_eq_real stdNormalLaw B).symm
      rw [← hmapZ, Measure.real, huniv, ENNReal.toReal_one]
    exact (stdNormalCDF_lt_one B).ne hcdf1

/-- At $\operatorname{Var}(W) = 0$, $\delta_0$ is a bounded zero-bias law of any mean-zero
$W \in L^2(P)$ with $|W| \le M$ a.s. (`SteinIntro.tex:1741-1742`, existence reading B2). -/
theorem isZeroBias_dirac_zero_of_variance_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {M : ℝ}
    (hW : MemLp W 2 P) (hmean : ∫ ω, W ω ∂P = 0)
    (hvar : ProbabilityTheory.variance W P = 0)
    (hbdd : ∀ᵐ ω ∂P, |W ω| ≤ M) :
    IsProbabilityMeasure (Measure.dirac (0 : ℝ)) ∧
      IsZeroBias P W (Measure.dirac (0 : ℝ)) id ∧
      ∀ᵐ x : ℝ ∂Measure.dirac 0, |x| ≤ M := by
  have hM : 0 ≤ M := nonneg_of_ae_abs_le P hbdd
  have hW0 : ∀ᵐ ω ∂P, W ω = 0 := by
    filter_upwards [ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hW hvar] with ω hω
    rwa [hmean] at hω
  refine ⟨inferInstance, ⟨hW, hmean, aemeasurable_id, fun f _ _ _ ↦ ?_⟩, ?_⟩
  · have hlhs : ∫ ω, W ω * f (W ω) ∂P = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hW0] with ω hω
      simp [hω]
    rw [hlhs, hvar, zero_mul]
  · exact (ae_dirac_iff (measurableSet_Iic.preimage continuous_abs.measurable)).mpr
      (by simpa using hM)

/-- Reduction of the existence reading (`Sec3_6_zeroBias_bdd_exists`, `SteinIntro.tex:1741-1742`)
to general zero-bias existence at positive variance (Proposition 3.19 in Track A). -/
theorem exists_bdd_zeroBias_of_pos_var_exists
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {M : ℝ}
    (hW : MemLp W 2 P) (hmean : ∫ ω, W ω ∂P = 0)
    (hbdd : ∀ᵐ ω ∂P, |W ω| ≤ M)
    (hexists_pos : 0 < ProbabilityTheory.variance W P →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ IsZeroBias P W ν id) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ IsZeroBias P W ν id ∧ ∀ᵐ x : ℝ ∂ν, |x| ≤ M := by
  rcases (ProbabilityTheory.variance_nonneg W P).eq_or_lt with hzero | hpos
  · exact ⟨Measure.dirac 0, isZeroBias_dirac_zero_of_variance_eq_zero P hW hmean hzero.symm hbdd⟩
  · obtain ⟨ν, hν_prob, hν_zb⟩ := hexists_pos hpos
    exact ⟨ν, hν_prob, hν_zb,
      @ae_abs_le_of_isZeroBias_of_ae_abs_le _ _ _ _ P _ ν hν_prob _ _ _ hpos hν_zb hbdd⟩

end SteinMethod
