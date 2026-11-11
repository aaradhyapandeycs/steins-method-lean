/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.MillRatio
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Moment Inequalities and Universal Cantelli–Normal Bound (`Formalization.BerryEsseen.Cantelli`)

Establishes moment helpers for standardized i.i.d. sums and the universal grid-free Cantelli bound
$\sup_{x \in \mathbb{R}} |\mu((-\infty, x]) - \Phi(x)| \le \frac{11}{20}$ for any mean-zero,
unit-variance probability measure $\mu$ on $\mathbb{R}$, handling the large-$\beta$ regime
($\beta = \rho / \sqrt{n} \ge 3 / 10$) of **Theorem 1.1** (`\label{thm1}`, `SteinIntro.tex:351-357`)
in Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped Real

namespace SteinMethod.BerryEsseen

/-! ### Section 1: $L^3$ Moment Helpers and $\mathbb{E}|X|^3 \ge 1$ -/

/-- On a probability space, `MemLp Y 3 P` implies `MemLp Y 2 P`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem memLp_two_of_memLp_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY3 : MemLp Y 3 P) :
    MemLp Y 2 P :=
  hY3.mono_exponent (by norm_num)

/-- On a probability space, `MemLp Y 3 P` implies `Integrable Y P`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integrable_of_memLp_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY3 : MemLp Y 3 P) :
    Integrable Y P :=
  memLp_one_iff_integrable.mp (hY3.mono_exponent (by norm_num))

/-- On a probability space, `MemLp Y 3 P` implies `Integrable (fun ω ↦ Y ω ^ 2) P`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integrable_sq_of_memLp_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY3 : MemLp Y 3 P) :
    Integrable (fun ω ↦ Y ω ^ 2) P :=
  (memLp_two_of_memLp_three hY3).integrable_sq

/-- `MemLp Y 3 P` implies integrability of `fun ω ↦ |Y ω| ^ 3`
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integrable_abs_cube_of_memLp_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hY3 : MemLp Y 3 P) :
    Integrable (fun ω ↦ |Y ω| ^ 3) P := by
  simpa [Real.norm_eq_abs] using hY3.integrable_norm_pow (by decide)

/-- If $\mathbb{E}[Y] = 0$ and $\operatorname{Var}(Y) = 1$, then $\mathbb{E}[Y^2] = 1$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem integral_sq_eq_one_of_mean_zero_var_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hYm : AEMeasurable Y P) (hmean : ∫ ω, Y ω ∂P = 0) (hvar : variance Y P = 1) :
    ∫ ω, Y ω ^ 2 ∂P = 1 := by
  have hv := variance_of_integral_eq_zero hYm hmean
  simpa [hv] using hvar

/-- Lyapunov lower bound $\mathbb{E}|Y|^3 \ge 1$ when $\mathbb{E}[Y] = 0$ and
$\operatorname{Var}(Y) = 1$, proved via $(|x| - 1)^2 (2|x| + 1) \ge 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem one_le_integral_abs_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY3 : MemLp Y 3 P) (hmean : ∫ ω, Y ω ∂P = 0) (hvar : variance Y P = 1) :
    1 ≤ ∫ ω, |Y ω| ^ 3 ∂P := by
  have hsq : ∫ ω, Y ω ^ 2 ∂P = 1 :=
    integral_sq_eq_one_of_mean_zero_var_one hY3.aemeasurable hmean hvar
  have hpt : ∀ ω, 3 * Y ω ^ 2 ≤ 2 * |Y ω| ^ 3 + 1 := fun ω ↦ by
    have h0 : 0 ≤ (|Y ω| - 1) ^ 2 * (2 * |Y ω| + 1) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have habs : |Y ω| ^ 2 = Y ω ^ 2 := sq_abs (Y ω)
    nlinarith
  have hint_l : Integrable (fun ω ↦ 3 * Y ω ^ 2) P :=
    (integrable_sq_of_memLp_three hY3).const_mul 3
  have hint_r : Integrable (fun ω ↦ 2 * |Y ω| ^ 3 + 1) P :=
    ((integrable_abs_cube_of_memLp_three hY3).const_mul 2).add (integrable_const 1)
  have hle := integral_mono hint_l hint_r hpt
  rw [integral_const_mul, hsq, mul_one,
    integral_add ((integrable_abs_cube_of_memLp_three hY3).const_mul 2) (integrable_const 1),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hle
  linarith

/-- Mean zero and unit second moment for the pushforward law `P.map W_n` of the standardized i.i.d.
sum $W_n = (\sum_{i=0}^{n-1} X_i) / \sqrt{n}$ (Theorem 1.1 `\label{thm1}`,
`SteinIntro.tex:351-357`). -/
theorem standardizedSum_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {n : ℕ} (hn : 0 < n)
    (hXm : ∀ i : ℕ, AEMeasurable (X i) P)
    (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX3 : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hvar : variance (X 0) P = 1) :
    let W : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / √n
    AEMeasurable W P ∧ IsProbabilityMeasure (P.map W) ∧
      Integrable (fun y : ℝ ↦ y) (P.map W) ∧ Integrable (fun y : ℝ ↦ y ^ 2) (P.map W) ∧
      (∫ y, y ∂(P.map W) = 0) ∧ (∫ y, y ^ 2 ∂(P.map W) = 1) := by
  intro W
  have hX2_0 : MemLp (X 0) 2 P := memLp_two_of_memLp_three hX3
  have hXi2 : ∀ i : ℕ, MemLp (X i) 2 P := fun i ↦ (hident i).symm.memLp_snd hX2_0
  have hXi1 : ∀ i : ℕ, Integrable (X i) P :=
    fun i ↦ memLp_one_iff_integrable.mp ((hXi2 i).mono_exponent (by norm_num))
  have hWm : AEMeasurable W P :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm i).div_const _
  have hprob : IsProbabilityMeasure (P.map W) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hWm MeasurableSet.univ, preimage_univ, measure_univ]⟩
  have hsum_Lp2 : MemLp (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) 2 P := by
    simpa using memLp_finsetSum (Finset.range n) (fun i _ ↦ hXi2 i)
  have hW_Lp2 : MemLp W 2 P := by
    simpa [W, div_eq_mul_inv] using hsum_Lp2.mul_const (√n)⁻¹
  have hW_int : Integrable W P :=
    memLp_one_iff_integrable.mp (hW_Lp2.mono_exponent (by norm_num))
  have hid_int : Integrable (fun y : ℝ ↦ y) (P.map W) :=
    (integrable_map_measure aestronglyMeasurable_id hWm).mpr hW_int
  have hid_sq_int : Integrable (fun y : ℝ ↦ y ^ 2) (P.map W) :=
    (integrable_map_measure (continuous_pow 2).aestronglyMeasurable hWm).mpr hW_Lp2.integrable_sq
  have hW_mean : ∫ ω, W ω ∂P = 0 := by
    simp_rw [W, div_eq_mul_inv, integral_mul_const]
    rw [integral_finsetSum _ fun i _ ↦ hXi1 i]
    have hi0 : ∀ i : ℕ, ∫ ω, X i ω ∂P = 0 := fun i ↦ by rw [(hident i).integral_eq, hmean]
    simp [hi0]
  have hsum_var : variance (∑ i ∈ Finset.range n, X i) P = n := by
    rw [IndepFun.variance_sum (fun i _ ↦ hXi2 i)
      (fun i _ j _ hij ↦ hindep.indepFun hij)]
    have hvi : ∀ i : ℕ, variance (X i) P = 1 := fun i ↦ by rw [(hident i).variance_eq, hvar]
    simp [hvi]
  have hW_var : variance W P = 1 := by
    have hWeq : W = (1 / √n) • ∑ i ∈ Finset.range n, X i := by
      ext ω; simp [W, div_eq_inv_mul]
    rw [hWeq, variance_smul, hsum_var]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [one_div, inv_pow, Real.sq_sqrt hn_pos.le, inv_mul_cancel₀ hn_pos.ne']
  have hW_sq : ∫ ω, W ω ^ 2 ∂P = 1 :=
    integral_sq_eq_one_of_mean_zero_var_one hWm hW_mean hW_var
  refine ⟨hWm, hprob, hid_int, hid_sq_int, ?_, ?_⟩
  · simpa using (integral_map hWm aestronglyMeasurable_id).trans hW_mean
  · rw [integral_map hWm (continuous_pow 2).aestronglyMeasurable]; exact hW_sq

/-! ### Section 2: Closed-Tail Cantelli Inequality and Universal `11 / 20` Bound -/

/-- Closed right-tail Cantelli inequality: for any probability measure $\mu$ on $\mathbb{R}$ with
mean $0$ and second moment $1$, $\mu([y, \infty)) \le \frac{1}{1 + y^2}$ for all $y > 0$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem cantelli_Ici {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun u : ℝ ↦ u) μ) (h2 : Integrable (fun u : ℝ ↦ u ^ 2) μ)
    (hm1 : ∫ u, u ∂μ = 0) (hm2 : ∫ u, u ^ 2 ∂μ = 1) {y : ℝ} (hy : 0 < y) :
    μ.real (Ici y) ≤ 1 / (1 + y ^ 2) := by
  have hc_pos : 0 < (1 + y ^ 2) / y := div_pos (by positivity) hy
  have hpt : ∀ u : ℝ, ((1 + y ^ 2) / y) ^ 2 * (Ici y).indicator 1 u ≤ (u + 1 / y) ^ 2 := by
    intro u
    by_cases hu : u ∈ Ici y
    · rw [indicator_of_mem hu, Pi.one_apply, mul_one]
      have huy : y ≤ u := hu
      have hle : (1 + y ^ 2) / y ≤ u + 1 / y := by
        have : (1 + y ^ 2) / y = y + 1 / y := by field_simp; ring
        linarith
      nlinarith
    · rw [indicator_of_notMem hu, mul_zero]; exact sq_nonneg _
  have hint_l : Integrable (fun u ↦ ((1 + y ^ 2) / y) ^ 2 * (Ici y).indicator 1 u) μ :=
    ((integrable_indicator_iff measurableSet_Ici).mpr integrableOn_const).const_mul _
  have hlin_c : Integrable (fun u : ℝ ↦ 2 / y * u + 1 / y ^ 2) μ :=
    (h1.const_mul (2 / y)).add (integrable_const _)
  have hint_r : Integrable (fun u : ℝ ↦ (u + 1 / y) ^ 2) μ := by
    have heq : (fun u : ℝ ↦ (u + 1 / y) ^ 2) =
        fun u ↦ u ^ 2 + (2 / y * u + 1 / y ^ 2) := by ext u; ring
    rw [heq]; exact h2.add hlin_c
  have hle := integral_mono hint_l hint_r hpt
  rw [integral_const_mul, integral_indicator_one measurableSet_Ici] at hle
  have hrhs : ∫ u, (u + 1 / y) ^ 2 ∂μ = (1 + y ^ 2) / y ^ 2 := by
    have heq : (fun u : ℝ ↦ (u + 1 / y) ^ 2) =
        fun u ↦ u ^ 2 + (2 / y * u + 1 / y ^ 2) := by ext u; ring
    rw [heq, integral_add h2 hlin_c,
      integral_add (h1.const_mul (2 / y)) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul, hm2, hm1, mul_zero, zero_add]
    field_simp; ring
  rw [hrhs] at hle
  have hden : 0 < ((1 + y ^ 2) / y) ^ 2 := sq_pos_of_pos hc_pos
  rw [← le_div_iff₀' hden] at hle
  refine hle.trans_eq ?_
  field_simp

/-- Closed left-tail Cantelli inequality: $\mu((-\infty, -y]) \le \frac{1}{1 + y^2}$ for $y > 0$
when $\mu$ has mean $0$ and second moment $1$ (Theorem 1.1 `\label{thm1}`,
`SteinIntro.tex:351-357`). -/
theorem cantelli_Iic_neg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun u : ℝ ↦ u) μ) (h2 : Integrable (fun u : ℝ ↦ u ^ 2) μ)
    (hm1 : ∫ u, u ∂μ = 0) (hm2 : ∫ u, u ^ 2 ∂μ = 1) {y : ℝ} (hy : 0 < y) :
    μ.real (Iic (-y)) ≤ 1 / (1 + y ^ 2) := by
  have hc_pos : 0 < (1 + y ^ 2) / y := div_pos (by positivity) hy
  have hpt : ∀ u : ℝ, ((1 + y ^ 2) / y) ^ 2 * (Iic (-y)).indicator 1 u ≤ (u - 1 / y) ^ 2 := by
    intro u
    by_cases hu : u ∈ Iic (-y)
    · rw [indicator_of_mem hu, Pi.one_apply, mul_one]
      have huy : u ≤ -y := hu
      have hle : (1 + y ^ 2) / y ≤ -(u - 1 / y) := by
        have : (1 + y ^ 2) / y = y + 1 / y := by field_simp; ring
        linarith
      have hsq : (-(u - 1 / y)) ^ 2 = (u - 1 / y) ^ 2 := neg_sq _
      nlinarith
    · rw [indicator_of_notMem hu, mul_zero]; exact sq_nonneg _
  have hint_l : Integrable (fun u ↦ ((1 + y ^ 2) / y) ^ 2 * (Iic (-y)).indicator 1 u) μ :=
    ((integrable_indicator_iff measurableSet_Iic).mpr integrableOn_const).const_mul _
  have hlin_c : Integrable (fun u : ℝ ↦ (-2 / y) * u + 1 / y ^ 2) μ :=
    (h1.const_mul (-2 / y)).add (integrable_const _)
  have hint_r : Integrable (fun u : ℝ ↦ (u - 1 / y) ^ 2) μ := by
    have heq : (fun u : ℝ ↦ (u - 1 / y) ^ 2) =
        fun u ↦ u ^ 2 + ((-2 / y) * u + 1 / y ^ 2) := by ext u; ring
    rw [heq]; exact h2.add hlin_c
  have hle := integral_mono hint_l hint_r hpt
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic] at hle
  have hrhs : ∫ u, (u - 1 / y) ^ 2 ∂μ = (1 + y ^ 2) / y ^ 2 := by
    have heq : (fun u : ℝ ↦ (u - 1 / y) ^ 2) =
        fun u ↦ u ^ 2 + ((-2 / y) * u + 1 / y ^ 2) := by ext u; ring
    rw [heq, integral_add h2 hlin_c,
      integral_add (h1.const_mul (-2 / y)) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul, hm2, hm1, mul_zero, zero_add]
    field_simp; ring
  rw [hrhs] at hle
  have hden : 0 < ((1 + y ^ 2) / y) ^ 2 := sq_pos_of_pos hc_pos
  rw [← le_div_iff₀' hden] at hle
  refine hle.trans_eq ?_
  field_simp

/-- Linear upper bound $\Phi(y) \le \frac{1}{2} + \frac{2}{5} y$ for $y \ge 0$, using
$\Phi'(t) = \phi(t) \le \phi(0) = (\sqrt{2\pi})^{-1} < 2 / 5$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem stdNormalCDF_le_half_add_two_fifths {y : ℝ} (hy : 0 ≤ y) :
    stdNormalCDF y ≤ 1 / 2 + 2 / 5 * y := by
  have hpdf0 : stdNormalPDF 0 ≤ 2 / 5 := by
    rw [stdNormalPDF_zero, inv_le_comm₀ (by positivity) (by norm_num),
      show ((2 / 5 : ℝ))⁻¹ = 5 / 2 by norm_num]
    have hpi : (25 / 4 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_d2]
    calc
      (5 / 2 : ℝ) = √((5 / 2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(2 * π) := Real.sqrt_le_sqrt (by norm_num; linarith)
  have hftc : ∫ t in (0 : ℝ)..y, stdNormalPDF t = stdNormalCDF y - stdNormalCDF 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hasDerivAt_stdNormalCDF t)
      (continuous_stdNormalPDF.intervalIntegrable 0 y)
  have hmono : ∫ t in (0 : ℝ)..y, stdNormalPDF t ≤ ∫ _ in (0 : ℝ)..y, (2 / 5 : ℝ) :=
    intervalIntegral.integral_mono_on hy (continuous_stdNormalPDF.intervalIntegrable 0 y)
      intervalIntegrable_const (fun t _ ↦ (stdNormalPDF_le_zero t).trans hpdf0)
  rw [hftc, intervalIntegral.integral_const, sub_zero, smul_eq_mul, stdNormalCDF_zero] at hmono
  linarith

private theorem rational_cantelli_aux {y : ℝ} (hy0 : 0 < y) :
    stdNormalCDF y - 1 + 1 / (1 + y ^ 2) ≤ 11 / 20 := by
  have hden : 0 < 1 + y ^ 2 := by positivity
  rcases le_or_gt y 1 with hy1 | hy1
  · have hphi := stdNormalCDF_le_half_add_two_fifths hy0.le
    have hpoly : 8 * y ^ 3 - 21 * y ^ 2 + 8 * y - 1 ≤ 0 := by
      rcases le_or_gt y (5 / 8) with hy58 | hy58
      · have h1 : 8 * y - 1 ≤ 16 * y ^ 2 := by nlinarith [sq_nonneg (4 * y - 1)]
        have h2 : y ^ 2 * (8 * y - 5) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith)
        linarith
      · have hcube : y ^ 3 ≤ y ^ 2 := by nlinarith
        have hquad : 0 ≤ (y - 5 / 8) * (13 * y + 1 / 8) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
    have hfrac : 1 / (1 + y ^ 2) ≤ 21 / 20 - 2 / 5 * y := by
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  · have hphi := stdNormalCDF_le_one y
    have htail : 1 / (1 + y ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hden (by norm_num)]
      nlinarith
    linarith

/-- Universal Cantelli–Normal bound: for any probability measure $\mu$ on $\mathbb{R}$ with mean $0$
and second moment $1$, $|\mu((-\infty, x]) - \Phi(x)| \le \frac{11}{20}$ for all $x \in \mathbb{R}$
(Theorem 1.1 `\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem abs_measureReal_Iic_sub_stdNormalCDF_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun u : ℝ ↦ u) μ) (h2 : Integrable (fun u : ℝ ↦ u ^ 2) μ)
    (hm1 : ∫ u, u ∂μ = 0) (hm2 : ∫ u, u ^ 2 ∂μ = 1) (x : ℝ) :
    |μ.real (Iic x) - stdNormalCDF x| ≤ 11 / 20 := by
  have hprob_nonneg : 0 ≤ μ.real (Iic x) := measureReal_nonneg
  have hprob_le_one : μ.real (Iic x) ≤ 1 := by
    have := measureReal_mono (subset_univ (Iic x)) (μ := μ)
    rwa [probReal_univ] at this
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hy : 0 < -x := neg_pos.mpr hx
    have hphi_le : stdNormalCDF x ≤ 1 / 2 := by
      rw [← stdNormalCDF_zero]; exact (strictMono_stdNormalCDF hx).le
    have hphi_nonneg : 0 ≤ stdNormalCDF x := stdNormalCDF_nonneg x
    have hcant : μ.real (Iic x) ≤ 1 / (1 + (-x) ^ 2) := by
      simpa using cantelli_Iic_neg h1 h2 hm1 hm2 hy
    have hphi_sym : stdNormalCDF x = 1 - stdNormalCDF (-x) := by
      simpa using stdNormalCDF_neg (-x)
    have haux := rational_cantelli_aux hy
    rw [abs_le]
    refine ⟨by linarith, ?_⟩
    linarith
  · rw [stdNormalCDF_zero, abs_le]
    constructor <;> linarith
  · have hphi_ge : 1 / 2 ≤ stdNormalCDF x := by
      rw [← stdNormalCDF_zero]; exact (strictMono_stdNormalCDF hx).le
    have hpart : μ.real (Iic x) + μ.real (Ioi x) = 1 := by
      rw [← measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
        Iic_union_Ioi, probReal_univ]
    have hioi : μ.real (Ioi x) ≤ 1 / (1 + x ^ 2) :=
      (measureReal_mono Ioi_subset_Ici_self).trans (cantelli_Ici h1 h2 hm1 hm2 hx)
    have haux := rational_cantelli_aux hx
    rw [abs_le]
    refine ⟨?_, by linarith⟩
    linarith

end SteinMethod.BerryEsseen
