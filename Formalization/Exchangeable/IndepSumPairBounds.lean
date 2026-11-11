/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.IndepSumPair
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Replace-One Sum Moment Bounds (`Formalization.Exchangeable.IndepSumPairBounds`)

Formalizes the cubic difference bound, conditional second-difference identity, conditional variance
estimate, and Theorem 3.7 right-hand-side assembly of Example 3.6
(`SteinIntro.tex:1071-1097`; `ISSUE-3.6`):
* `indepSum_replaceOne_lintegral_abs_sub_cube_le`:
  $\mathbb{E}|W' - W|^3 \le \frac{8}{n^{5/2}} \sum_{i=1}^n \mathbb{E}|X_i|^3$
  (`SteinIntro.tex:1071-1077`; `ISSUE-3.6`).
* `indepSum_replaceOne_condExp_sq_sub_vx_ae_eq` and
  `indepSum_replaceOne_evariance_condExp_sq_sub_le`:
  $\mathbb{E}[(W' - W)^2 \mid X_1, \dots, X_n] = n^{-2} \sum_{i=1}^n (1 + X_i^2)$ a.s. and
  $\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W]) \le n^{-4} \sum_{i=1}^n \mathbb{E}[X_i^4]$
  (`SteinIntro.tex:1078-1086`).
* `indepSum_replaceOne_thm3_7_rhs_le_corrected` and
  `indepSum_replaceOne_corrected_rhs_le_restricted`: algebraic simplification of the Theorem 3.7
  right-hand side at $a = 1/n$ for all $n \ge 1$ (`Ex3_6_corrected`) and for $n \ge 16$
  (`Ex3_6_restricted`, `SteinIntro.tex:1087-1097`; `ISSUE-3.6`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SteinMethod

/-- Elementary cubic inequality $|a - b|^3 \le 4(|a|^3 + |b|^3)$ (`SteinIntro.tex:1074`;
`ISSUE-3.6`). -/
private lemma abs_sub_cube_le (a b : ℝ) : |a - b| ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
  have hsub : |a - b| ≤ |a| + |b| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  have ha : 0 ≤ |a| := abs_nonneg a
  have hb : 0 ≤ |b| := abs_nonneg b
  have hab : 0 ≤ |a - b| := abs_nonneg (a - b)
  have hpow : |a - b| ^ 3 ≤ (|a| + |b|) ^ 3 := by
    have hid : (|a| + |b|) ^ 3 - |a - b| ^ 3 =
        (|a| + |b| - |a - b|) * ((|a| + |b|) ^ 2 + (|a| + |b|) * |a - b| + |a - b| ^ 2) := by ring
    have hfac1 : 0 ≤ |a| + |b| - |a - b| := sub_nonneg.mpr hsub
    have hfac2 : 0 ≤ (|a| + |b|) ^ 2 + (|a| + |b|) * |a - b| + |a - b| ^ 2 :=
      add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (add_nonneg ha hb) hab)) (sq_nonneg _)
    have hnn : 0 ≤ (|a| + |b|) ^ 3 - |a - b| ^ 3 := hid ▸ mul_nonneg hfac1 hfac2
    linarith
  have hfour : (|a| + |b|) ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
    have hid : 4 * (|a| ^ 3 + |b| ^ 3) - (|a| + |b|) ^ 3 =
        3 * (|a| + |b|) * (|a| - |b|) ^ 2 := by ring
    have hnn : 0 ≤ 3 * (|a| + |b|) * (|a| - |b|) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (add_nonneg ha hb)) (sq_nonneg _)
    linarith
  exact hpow.trans hfour

/-- Example 3.6, corrected third absolute difference bound (`SteinIntro.tex:1071-1077`;
`ISSUE-3.6`):
$\mathbb{E}|W' - W|^3 \le \frac{8}{n^{5/2}} \sum_{i=1}^n \mathbb{E}|X_i|^3$. -/
theorem indepSum_replaceOne_lintegral_abs_sub_cube_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ (5 / 2 : ℝ) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
  intro W W'
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hrn_pos
  have habs_meas : Measurable (abs : ℝ → ℝ) := continuous_abs.measurable
  have hIk_meas : ∀ i : Fin n, MeasurableSet {ω : Ω | I ω = i} := by
    intro i
    have hpre : {ω : Ω | I ω = i} = I ⁻¹' {i} := by ext ω; simp
    exact hpre ▸ hI_meas (measurableSet_singleton i)
  have hX3_int : ∀ i : Fin n, Integrable (fun ω ↦ |X i ω| ^ 3) P := by
    intro i
    have h3 : MemLp (X i) 3 P := (hX4 i).mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4)
    simpa only [Real.norm_eq_abs] using h3.integrable_norm_pow'
  have hX'3_int : ∀ i : Fin n, Integrable (fun ω ↦ |X' i ω| ^ 3) P := by
    intro i
    have hId_i : IdentDistrib (X' i) (X i) P P := hId.comp (measurable_pi_apply i)
    have h3 : MemLp (X' i) 3 P :=
      (hId_i.memLp_iff.mpr (hX4 i)).mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4)
    simpa only [Real.norm_eq_abs] using h3.integrable_norm_pow'
  let U : Ω → ℝ := fun ω ↦ ∑ i : Fin n,
    {ω' : Ω | I ω' = i}.indicator
      (fun ω' ↦ 4 * (|X' i ω'| ^ 3 + |X i ω'| ^ 3) / Real.sqrt n ^ 3) ω
  have hU_term_int : ∀ i : Fin n, Integrable
      ({ω' : Ω | I ω' = i}.indicator
        (fun ω' ↦ 4 * (|X' i ω'| ^ 3 + |X i ω'| ^ 3) / Real.sqrt n ^ 3)) P :=
    fun i ↦
      ((((hX'3_int i).fun_add (hX3_int i)).const_mul 4).div_const (Real.sqrt n ^ 3)).indicator
        (hIk_meas i)
  have hU_int : Integrable U P := integrable_finsetSum Finset.univ fun i _ ↦ hU_term_int i
  have hU_nonneg : ∀ ω : Ω, 0 ≤ U ω := by
    intro ω
    refine Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun ω' _ ↦ ?_) ω
    positivity
  have hpt_le : ∀ ω : Ω, |W' ω - W ω| ^ 3 ≤ U ω := by
    intro ω
    have hdiff : W' ω - W ω = (X' (I ω) ω - X (I ω) ω) / Real.sqrt n := by dsimp [W']; ring
    have hU_eval :
        U ω = 4 * (|X' (I ω) ω| ^ 3 + |X (I ω) ω| ^ 3) / Real.sqrt n ^ 3 := by
      have hterm : ∀ i : Fin n,
          {ω' : Ω | I ω' = i}.indicator
              (fun ω' ↦ 4 * (|X' i ω'| ^ 3 + |X i ω'| ^ 3) / Real.sqrt n ^ 3) ω =
            if I ω = i then 4 * (|X' i ω| ^ 3 + |X i ω| ^ 3) / Real.sqrt n ^ 3 else 0 := by
        intro i; by_cases hi : I ω = i <;> simp [hi]
      dsimp [U]
      simp_rw [hterm]
      simp
    rw [hdiff, abs_div, abs_of_pos hsqrt_pos, div_pow, hU_eval]
    exact div_le_div_of_nonneg_right (abs_sub_cube_le (X' (I ω) ω) (X (I ω) ω)) (by positivity)
  have hL_le :
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) ≤ ENNReal.ofReal (∫ ω, U ω ∂P) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P)
          ≤ ∫⁻ ω, ENNReal.ofReal (U ω) ∂P :=
            lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (hpt_le ω)
      _ = ENNReal.ofReal (∫ ω, U ω ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal hU_int
              (Filter.Eventually.of_forall hU_nonneg)).symm
  have hrpow_eq : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) * Real.sqrt n ^ 3 := by
    have h52 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt n := by
      rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / (2 : ℝ) by norm_num,
        Real.rpow_add hrn_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    have hsq3 : Real.sqrt n ^ 3 = (n : ℝ) * Real.sqrt n := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, Real.sq_sqrt hrn_pos.le]
    rw [h52, hsq3]
    ring
  have hIntU :
      ∫ ω, U ω ∂P = 8 / (n : ℝ) ^ (5 / 2 : ℝ) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    rw [integral_finsetSum Finset.univ fun i _ ↦ hU_term_int i]
    have hterm : ∀ i : Fin n,
        ∫ ω, {ω' : Ω | I ω' = i}.indicator
            (fun ω' ↦ 4 * (|X' i ω'| ^ 3 + |X i ω'| ^ 3) / Real.sqrt n ^ 3) ω ∂P =
          8 / (n : ℝ) ^ (5 / 2 : ℝ) * ∫ ω, |X i ω| ^ 3 ∂P := by
      intro i
      let Hi : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
        fun p ↦ 4 * (|p.2 i| ^ 3 + |p.1 i| ^ 3) / Real.sqrt n ^ 3
      have hHi_meas : Measurable Hi := by
        have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ |p.2 i| ^ 3) :=
          (habs_meas.comp ((measurable_pi_apply i).comp measurable_snd)).pow_const 3
        have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ |p.1 i| ^ 3) :=
          (habs_meas.comp ((measurable_pi_apply i).comp measurable_fst)).pow_const 3
        exact ((h1.add h2).const_mul 4).div_const (Real.sqrt n ^ 3)
      have hStep :=
        indepSum_setIntegral_indicator_I_vx P hn hX_meas hX'_meas hI_meas hI_indep hI_unif i
          MeasurableSet.univ hHi_meas
      simp only [Set.preimage_univ, Measure.restrict_univ] at hStep
      have hId_abs3 : ∫ ω, |X' i ω| ^ 3 ∂P = ∫ ω, |X i ω| ^ 3 ∂P :=
        ((hId.comp (measurable_pi_apply i)).comp (habs_meas.pow_const 3)).integral_eq
      rw [hStep]
      dsimp [Hi]
      rw [integral_div, integral_const_mul, integral_add (hX'3_int i) (hX3_int i), hId_abs3,
        hrpow_eq, one_div]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hterm i
  rwa [hIntU] at hL_le

/-- Example 3.6, conditional second difference given $(X_1, \dots, X_n)$
(`SteinIntro.tex:1078-1082`):
$\mathbb{E}[(W' - W)^2 \mid X_1, \dots, X_n] = \frac{1}{n^2} \sum_{i=1}^n (1 + X_i^2)$ a.s. -/
theorem indepSum_replaceOne_condExp_sq_sub_vx_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
      fun ω ↦ (1 / (n : ℝ) ^ 2) * ∑ i : Fin n, (1 + X i ω ^ 2) := by
  intro W W'
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  let VX' : Ω → Fin n → ℝ := fun ω i ↦ X' i ω
  let VXX' : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (VX ω, VX' ω)
  let g : Ω → ℝ := fun ω ↦ (1 / (n : ℝ) ^ 2) * ∑ i : Fin n, (1 + X i ω ^ 2)
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hmVX := hVX_meas.comap_le
  have hX2 : ∀ i : Fin n, MemLp (X i) 2 P :=
    fun i ↦ (hX4 i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hX'2 : ∀ i : Fin n, MemLp (X' i) 2 P := by
    intro i
    have hId_i : IdentDistrib (X' i) (X i) P P := hId.comp (measurable_pi_apply i)
    exact (hId_i.memLp_iff.mpr (hX4 i)).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hX_sq_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 2) P := fun i ↦ (hX2 i).integrable_sq
  have hX'_sq_int : ∀ i : Fin n, Integrable (fun ω ↦ X' i ω ^ 2) P :=
    fun i ↦ (hX'2 i).integrable_sq
  have hXX'_mul_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω * X' i ω) P :=
    fun i ↦ (hX2 i).integrable_mul (hX'2 i)
  have hIk_meas : ∀ i : Fin n, MeasurableSet {ω : Ω | I ω = i} := by
    intro i
    have hpre : {ω : Ω | I ω = i} = I ⁻¹' {i} := by ext ω; simp
    exact hpre ▸ hI_meas (measurableSet_singleton i)
  have hY_decomp :
      (fun ω ↦ (W' ω - W ω) ^ 2) =
        fun ω ↦ ∑ i : Fin n,
          {ω' : Ω | I ω' = i}.indicator (fun ω' ↦ (X' i ω' - X i ω') ^ 2 / (n : ℝ)) ω := by
    funext ω
    have hdiff : (W' ω - W ω) ^ 2 = (X' (I ω) ω - X (I ω) ω) ^ 2 / (n : ℝ) := by
      have hd : W' ω - W ω = (X' (I ω) ω - X (I ω) ω) / Real.sqrt n := by dsimp [W']; ring
      rw [hd, div_pow, Real.sq_sqrt hrn_pos.le]
    have hsum :
        (∑ i : Fin n,
            {ω' : Ω | I ω' = i}.indicator (fun ω' ↦ (X' i ω' - X i ω') ^ 2 / (n : ℝ)) ω) =
          (X' (I ω) ω - X (I ω) ω) ^ 2 / (n : ℝ) := by
      have hterm : ∀ i : Fin n,
          {ω' : Ω | I ω' = i}.indicator (fun ω' ↦ (X' i ω' - X i ω') ^ 2 / (n : ℝ)) ω =
            if I ω = i then (X' i ω - X i ω) ^ 2 / (n : ℝ) else 0 := by
        intro i; by_cases hi : I ω = i <;> simp [hi]
      simp_rw [hterm]
      simp
    exact hdiff.trans hsum.symm
  have hTerm_int : ∀ i : Fin n, Integrable
      ({ω' : Ω | I ω' = i}.indicator (fun ω' ↦ (X' i ω' - X i ω') ^ 2 / (n : ℝ))) P :=
    fun i ↦ ((((hX'2 i).sub (hX2 i)).integrable_sq).div_const (n : ℝ)).indicator (hIk_meas i)
  have hY_int : Integrable (fun ω ↦ (W' ω - W ω) ^ 2) P :=
    hY_decomp ▸ integrable_finsetSum Finset.univ fun i _ ↦ hTerm_int i
  have hg_int : Integrable g P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ (integrable_const (1 : ℝ)).fun_add (hX_sq_int i))
      |>.const_mul (1 / (n : ℝ) ^ 2)
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap VX inferInstance] g := by
    let g0 : (Fin n → ℝ) → ℝ := fun v ↦ (1 / (n : ℝ) ^ 2) * ∑ i : Fin n, (1 + v i ^ 2)
    have hg0_meas : Measurable g0 :=
      (Finset.measurable_sum Finset.univ fun i _ ↦
        measurable_const.add ((measurable_pi_apply i).pow_const 2)).const_mul (1 / (n : ℝ) ^ 2)
    exact (hg0_meas.comp (comap_measurable (m := inferInstance) VX)).stronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmVX hY_int
    (fun s _ _ ↦ hg_int.integrableOn)
    (fun s hs _ ↦ ?_)
    hg_sm.aestronglyMeasurable).symm
  rcases hs with ⟨T, hT, rfl⟩
  rw [hY_decomp, integral_finsetSum Finset.univ fun i _ ↦ (hTerm_int i).integrableOn]
  have hterm_eq : ∀ i : Fin n,
      ∫ ω in VX ⁻¹' T,
          {ω' : Ω | I ω' = i}.indicator (fun ω' ↦ (X' i ω' - X i ω') ^ 2 / (n : ℝ)) ω ∂P =
        (1 / (n : ℝ) ^ 2) * ∫ ω in VX ⁻¹' T, (1 + X i ω ^ 2) ∂P := by
    intro i
    let Hi : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ (p.2 i - p.1 i) ^ 2 / (n : ℝ)
    have hHi_meas : Measurable Hi := by
      have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      exact ((h1.sub h2).pow_const 2).div_const (n : ℝ)
    have hStep :=
      indepSum_setIntegral_indicator_I_vx P hn hX_meas hX'_meas hI_meas hI_indep hI_unif i hT
        hHi_meas
    have hId_i : IdentDistrib (X' i) (X i) P P := hId.comp (measurable_pi_apply i)
    have hX'0 : ∫ ω, X' i ω ∂P = 0 := hId_i.integral_eq.trans (hX0 i)
    have hX_sq1 : ∫ ω, X i ω ^ 2 ∂P = 1 := by
      rw [← ProbabilityTheory.variance_of_integral_eq_zero (hX_meas i).aemeasurable (hX0 i),
        hX_var i]
    have hX'_sq1 : ∫ ω, X' i ω ^ 2 ∂P = 1 := hId_i.sq.integral_eq.trans hX_sq1
    have hIntX'_sq : ∫ ω in VX ⁻¹' T, X' i ω ^ 2 ∂P = ∫ ω in VX ⁻¹' T, (1 : ℝ) ∂P := by
      have hmul :=
        indepSum_setIntegral_vx_mul_vx' P hX_meas hX'_meas hXX'_indep hT
          (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (1 : ℝ)))
          ((measurable_pi_apply i).pow_const 2)
      simpa only [one_mul, hX'_sq1, mul_one] using hmul
    have hIntCross : ∫ ω in VX ⁻¹' T, X i ω * X' i ω ∂P = 0 := by
      have hmul :=
        indepSum_setIntegral_vx_mul_vx' P hX_meas hX'_meas hXX'_indep hT
          (measurable_pi_apply i) (measurable_pi_apply i)
      simpa only [hX'0, mul_zero] using hmul
    have hexp :
        (fun ω ↦ Hi (VXX' ω)) =
          fun ω ↦ ((X' i ω ^ 2 + X i ω ^ 2) - 2 * (X i ω * X' i ω)) / (n : ℝ) := by
      funext ω; dsimp [Hi, VXX', VX, VX']; ring
    have hEvalHi :
        ∫ ω in VX ⁻¹' T, Hi (VXX' ω) ∂P =
          (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, (1 + X i ω ^ 2) ∂P := by
      rw [hexp, integral_div,
        integral_sub ((hX'_sq_int i).fun_add (hX_sq_int i)).integrableOn
          ((hXX'_mul_int i).const_mul 2).integrableOn,
        integral_add (hX'_sq_int i).integrableOn (hX_sq_int i).integrableOn,
        integral_const_mul 2 (fun ω ↦ X i ω * X' i ω), hIntX'_sq, hIntCross,
        integral_add (integrable_const (1 : ℝ)).integrableOn (hX_sq_int i).integrableOn]
      ring
    rw [hStep, hEvalHi]
    ring
  calc
    ∫ ω in VX ⁻¹' T, g ω ∂P
        = (1 / (n : ℝ) ^ 2) *
            ∫ ω in VX ⁻¹' T, (∑ i : Fin n, (1 + X i ω ^ 2)) ∂P :=
          integral_const_mul (1 / (n : ℝ) ^ 2) _
    _ = (1 / (n : ℝ) ^ 2) * ∑ i : Fin n, ∫ ω in VX ⁻¹' T, (1 + X i ω ^ 2) ∂P := by
          rw [integral_finsetSum Finset.univ fun i _ ↦
            ((integrable_const (1 : ℝ)).fun_add (hX_sq_int i)).integrableOn]
    _ = ∑ i : Fin n, (1 / (n : ℝ) ^ 2) * ∫ ω in VX ⁻¹' T, (1 + X i ω ^ 2) ∂P := by
          rw [Finset.mul_sum]
    _ = ∑ i : Fin n,
          ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = i}.indicator (fun ω' ↦ (X' i ω' - X i ω') ^ 2 / (n : ℝ)) ω ∂P :=
          Finset.sum_congr rfl fun i _ ↦ (hterm_eq i).symm

/-- Example 3.6, conditional variance estimate (`SteinIntro.tex:1078-1086`):
$\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W]) \le \frac{1}{n^4} \sum_{i=1}^n \mathbb{E}[X_i^4]$
in `ℝ≥0∞` (`ProbabilityTheory.evariance`). -/
theorem indepSum_replaceOne_evariance_condExp_sq_sub_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    ProbabilityTheory.evariance
        (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ≤
      ENNReal.ofReal ((1 / (n : ℝ) ^ 4) * ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) := by
  intro W W'
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  let Y : Ω → ℝ := fun ω ↦ (W' ω - W ω) ^ 2
  let g : Ω → ℝ := fun ω ↦ (1 / (n : ℝ) ^ 2) * ∑ i : Fin n, (1 + X i ω ^ 2)
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hW_meas : Measurable W :=
    (Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i).div_const (Real.sqrt n)
  have hmW := hW_meas.comap_le
  have hmVX := hVX_meas.comap_le
  have hmW_le_mVX :
      MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap VX inferInstance := by
    intro s hs
    rcases hs with ⟨B, hB, rfl⟩
    let sumScale : (Fin n → ℝ) → ℝ := fun v ↦ (∑ i : Fin n, v i) / Real.sqrt n
    have hsumScale_meas : Measurable sumScale :=
      (Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i).div_const (Real.sqrt n)
    exact ⟨sumScale ⁻¹' B, hsumScale_meas hB, rfl⟩
  have hCondVX : P[Y | MeasurableSpace.comap VX inferInstance] =ᵐ[P] g :=
    indepSum_replaceOne_condExp_sq_sub_vx_ae_eq P hn hX_meas hX'_meas hX4 hX0 hX_var
      hId hXX'_indep hI_meas hI_indep hI_unif
  have hTower :
      P[Y | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        P[g | MeasurableSpace.comap W inferInstance] :=
    (condExp_condExp_of_le hmW_le_mVX hmVX).symm.trans (condExp_congr_ae hCondVX)
  have hX4_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 4) P := by
    intro i
    have hpow : (fun ω ↦ ‖X i ω‖ ^ 4) = fun ω ↦ X i ω ^ 4 := by
      funext ω
      rw [Real.norm_eq_abs]
      have hsq : |X i ω| ^ 2 = X i ω ^ 2 := sq_abs (X i ω)
      calc
        |X i ω| ^ 4 = (|X i ω| ^ 2) ^ 2 := by ring
        _ = (X i ω ^ 2) ^ 2 := by rw [hsq]
        _ = X i ω ^ 4 := by ring
    exact hpow ▸ (hX4 i).integrable_norm_pow'
  have hXsq_L2 : ∀ i : Fin n, MemLp (fun ω ↦ X i ω ^ 2) 2 P := by
    intro i
    refine (memLp_two_iff_integrable_sq
      ((hX_meas i).pow_const 2).stronglyMeasurable.aestronglyMeasurable).mpr ?_
    have heq : (fun ω ↦ (X i ω ^ 2) ^ 2) = fun ω ↦ X i ω ^ 4 := by funext ω; ring
    exact heq ▸ hX4_int i
  have hZ_L2 : ∀ i : Fin n, MemLp (fun ω ↦ 1 + X i ω ^ 2) 2 P :=
    fun i ↦ (memLp_const (1 : ℝ)).add (hXsq_L2 i)
  have hg_L2 : MemLp g 2 P :=
    (memLp_finsetSum Finset.univ fun i _ ↦ hZ_L2 i).const_mul (1 / (n : ℝ) ^ 2)
  have hgW_L2 : MemLp (P[g | MeasurableSpace.comap W inferInstance]) 2 P :=
    hg_L2.condExp one_le_two
  have hVarCondLe :
      ProbabilityTheory.variance (P[g | MeasurableSpace.comap W inferInstance]) P ≤
        ProbabilityTheory.variance g P := by
    have hnorm2 : ∀ f : Ω → ℝ, (fun ω ↦ ‖f ω‖ ^ (2 : ℝ)) = fun ω ↦ f ω ^ 2 := by
      intro f; funext ω
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have hSqLe :
        ∫ ω, (P[g | MeasurableSpace.comap W inferInstance] ω) ^ 2 ∂P ≤ ∫ ω, g ω ^ 2 ∂P := by
      have h :=
        integral_norm_condExp_rpow_le
          (m := MeasurableSpace.comap W inferInstance) (μ := P) (one_le_two : (1 : ℝ) ≤ 2)
          ((hnorm2 g).symm ▸ hg_L2.integrable_sq)
      simpa only [hnorm2] using h
    have hMeanEq :
        ∫ ω, P[g | MeasurableSpace.comap W inferInstance] ω ∂P = ∫ ω, g ω ∂P :=
      integral_condExp hmW
    rw [ProbabilityTheory.variance_eq_sub hgW_L2, ProbabilityTheory.variance_eq_sub hg_L2]
    simp only [Pi.pow_apply, hMeanEq]
    linarith
  have hVarGLe :
      ProbabilityTheory.variance g P ≤ (1 / (n : ℝ) ^ 4) * ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P := by
    have hg_eq : g = fun ω ↦ (1 / (n : ℝ) ^ 2) * (∑ i : Fin n, fun ω' ↦ 1 + X i ω' ^ 2) ω := by
      funext ω; simp [g]
    have hZ_indep : ProbabilityTheory.iIndepFun (fun i ω ↦ 1 + X i ω ^ 2) P :=
      h_indep.comp (fun _ ↦ fun x : ℝ ↦ 1 + x ^ 2)
        (fun _ ↦ measurable_const.add (measurable_id.pow_const 2))
    rw [hg_eq, ProbabilityTheory.variance_const_mul,
      ProbabilityTheory.IndepFun.variance_sum (fun i _ ↦ hZ_L2 i)
        (fun i _ j _ hij ↦ hZ_indep.indepFun hij)]
    have hpow4 : (1 / (n : ℝ) ^ 2) ^ 2 = 1 / (n : ℝ) ^ 4 := by ring
    rw [hpow4]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ ?_) (by positivity)
    rw [ProbabilityTheory.variance_const_add
      ((hX_meas i).pow_const 2).stronglyMeasurable.aestronglyMeasurable 1]
    have hle := ProbabilityTheory.variance_le_expectation_sq (μ := P)
      ((hX_meas i).pow_const 2).stronglyMeasurable.aestronglyMeasurable
    have heq4 : (fun ω ↦ ((fun ω' ↦ X i ω' ^ 2) ^ 2) ω) = fun ω ↦ X i ω ^ 4 := by
      funext ω; simp only [Pi.pow_apply]; ring
    exact heq4 ▸ hle
  rw [ProbabilityTheory.evariance_congr hTower, ← ProbabilityTheory.ofReal_variance hgW_L2]
  exact ENNReal.ofReal_le_ofReal (hVarCondLe.trans hVarGLe)

/-- Example 3.6, assembly of the corrected Wasserstein right-hand side from Theorem 3.7 at
$a = 1/n$ (`SteinIntro.tex:1087-1097`; `ISSUE-3.6`). -/
theorem indepSum_replaceOne_thm3_7_rhs_le_corrected
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (Real.sqrt (2 * Real.pi) * (1 / (n : ℝ))) +
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * (1 / (n : ℝ))) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
  intro W W'
  let S4 : ℝ := ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P
  let S3 : ℝ := ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hS4_nn : 0 ≤ S4 :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ by positivity
  have hS3_nn : 0 ≤ S3 :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ by positivity
  have hEvar :=
    indepSum_replaceOne_evariance_condExp_sq_sub_le P hn hX_meas hX'_meas h_indep hX4 hX0 hX_var
      hId hXX'_indep hI_meas hI_indep hI_unif
  have hCube :=
    indepSum_replaceOne_lintegral_abs_sub_cube_le P hn hX_meas hX'_meas hX4 hId hI_meas hI_indep
      hI_unif
  -- First summand simplification.
  let r1 : ℝ := Real.sqrt (2 / Real.pi)
  let r2 : ℝ := Real.sqrt (2 * Real.pi)
  have hr2_pos : 0 < r2 := Real.sqrt_pos.mpr (by positivity)
  have hr12 : r1 * r2 = 2 := by
    dsimp [r1, r2]
    rw [← Real.sqrt_mul (by positivity)]
    have hprod : (2 / Real.pi) * (2 * Real.pi) = (2 : ℝ) ^ 2 := by
      calc
        (2 / Real.pi) * (2 * Real.pi) = 4 * (Real.pi⁻¹ * Real.pi) := by ring
        _ = (2 : ℝ) ^ 2 := by rw [inv_mul_cancel₀ hpi_pos.ne']; norm_num
    rw [hprod, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hr2_inv : r2⁻¹ = r1 * (2 : ℝ)⁻¹ := by
    calc
      r2⁻¹ = (r1 * r2 * (2 : ℝ)⁻¹) * r2⁻¹ := by
        rw [hr12, mul_inv_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_mul]
      _ = r1 * (2 : ℝ)⁻¹ * (r2 * r2⁻¹) := by ring
      _ = r1 * (2 : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hr2_pos.ne', mul_one]
  have hAlg1 :
      (((1 / (n : ℝ) ^ 4) * S4) ^ (1 / 2 : ℝ)) / (r2 * (1 / (n : ℝ))) =
        r1 * Real.sqrt S4 / (2 * (n : ℝ)) := by
    have hnum :
        ((1 / (n : ℝ) ^ 4) * S4) ^ (1 / 2 : ℝ) = (1 / (n : ℝ) ^ 2) * Real.sqrt S4 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
        show (1 / (n : ℝ) ^ 4) = (1 / (n : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [hnum]
    calc
      ((1 / (n : ℝ) ^ 2) * Real.sqrt S4) / (r2 * (1 / (n : ℝ)))
          = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * (n : ℝ)) * r2⁻¹ * Real.sqrt S4 := by
            rw [one_div, one_div]
            simp only [sq, div_eq_mul_inv, mul_inv_rev, inv_inv]
            ring
      _ = (n : ℝ)⁻¹ * (r1 * (2 : ℝ)⁻¹) * Real.sqrt S4 := by
            rw [inv_mul_cancel₀ hrn_pos.ne', mul_one, hr2_inv]
      _ = r1 * Real.sqrt S4 * ((n : ℝ)⁻¹ * (2 : ℝ)⁻¹) := by ring
      _ = r1 * Real.sqrt S4 / (2 * (n : ℝ)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
  have hTerm1 :
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (r2 * (1 / (n : ℝ))) ≤
        ENNReal.ofReal (r1 * Real.sqrt S4 / (2 * (n : ℝ))) := by
    calc
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (r2 * (1 / (n : ℝ)))
          ≤ ENNReal.ofReal ((1 / (n : ℝ) ^ 4) * S4) ^ (1 / 2 : ℝ) /
              ENNReal.ofReal (r2 * (1 / (n : ℝ))) :=
            ENNReal.div_le_div_right (ENNReal.rpow_le_rpow hEvar (by positivity)) _
      _ = ENNReal.ofReal ((((1 / (n : ℝ) ^ 4) * S4) ^ (1 / 2 : ℝ)) / (r2 * (1 / (n : ℝ)))) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) hS4_nn) (by positivity),
              ← ENNReal.ofReal_div_of_pos (mul_pos hr2_pos (by positivity))]
      _ = ENNReal.ofReal (r1 * Real.sqrt S4 / (2 * (n : ℝ))) := by rw [hAlg1]
  -- Second summand simplification.
  have hAlg2 :
      (8 / (n : ℝ) ^ (5 / 2 : ℝ) * S3) / (3 * (1 / (n : ℝ))) =
        8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * S3 := by
    let p : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)
    have hp : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) * p := by
      dsimp [p]
      rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hrn_pos, Real.rpow_one]
    rw [hp]
    calc
      (8 / ((n : ℝ) * p) * S3) / (3 * (1 / (n : ℝ)))
          = 8 * (p⁻¹ * (n : ℝ)⁻¹) * S3 * ((n : ℝ)⁻¹⁻¹ * (3 : ℝ)⁻¹) := by
            rw [one_div]
            simp only [div_eq_mul_inv, mul_inv_rev]
      _ = 8 * (p⁻¹ * (3 : ℝ)⁻¹) * ((n : ℝ)⁻¹ * (n : ℝ)) * S3 := by
            rw [inv_inv]; ring
      _ = 8 * (p⁻¹ * (3 : ℝ)⁻¹) * S3 := by
            rw [inv_mul_cancel₀ hrn_pos.ne', mul_one]
      _ = 8 / (3 * p) * S3 := by
            simp only [div_eq_mul_inv, mul_inv_rev]
  have hTerm2 :
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * (1 / (n : ℝ))) ≤
        ENNReal.ofReal (8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * S3) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * (1 / (n : ℝ)))
          ≤ ENNReal.ofReal (8 / (n : ℝ) ^ (5 / 2 : ℝ) * S3) /
              ENNReal.ofReal (3 * (1 / (n : ℝ))) :=
            ENNReal.div_le_div_right hCube _
      _ = ENNReal.ofReal ((8 / (n : ℝ) ^ (5 / 2 : ℝ) * S3) / (3 * (1 / (n : ℝ)))) := by
            rw [← ENNReal.ofReal_div_of_pos (by positivity)]
      _ = ENNReal.ofReal (8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * S3) := by rw [hAlg2]
  have hp_pos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hrn_pos (3 / 2)
  have hnn1 : 0 ≤ r1 * Real.sqrt S4 / (2 * (n : ℝ)) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
  have hnn2 : 0 ≤ 8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * S3 :=
    mul_nonneg (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hp_pos.le)) hS3_nn
  calc
    ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (r2 * (1 / (n : ℝ))) +
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * (1 / (n : ℝ)))
        ≤ ENNReal.ofReal (r1 * Real.sqrt S4 / (2 * (n : ℝ))) +
            ENNReal.ofReal (8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * S3) :=
          add_le_add hTerm1 hTerm2
    _ = ENNReal.ofReal
          (r1 * Real.sqrt S4 / (2 * (n : ℝ)) +
            8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * S3) :=
          (ENNReal.ofReal_add hnn1 hnn2).symm

/-- Example 3.6, comparison between the corrected bound and the printed bound for $n \ge 16$
(`SteinIntro.tex:1053-1097`, `L1089`; `ISSUE-3.6`): for $n \ge 16$,
$\frac{8}{3 n^{3/2}} \le \frac{2}{3n}$. -/
theorem indepSum_replaceOne_corrected_rhs_le_restricted
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn16 : 16 ≤ n) {X : Fin n → Ω → ℝ} :
    ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
  have hn : 0 < n := by omega
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hrn_pos
  have h16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn16
  have h4_le_sqrt : (4 : ℝ) ≤ Real.sqrt n := by
    calc
      (4 : ℝ) = Real.sqrt ((4 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  have hratio_le_one : 4 / Real.sqrt n ≤ 1 := by
    calc
      4 / Real.sqrt n = 4 * (Real.sqrt n)⁻¹ := div_eq_mul_inv 4 (Real.sqrt n)
      _ ≤ Real.sqrt n * (Real.sqrt n)⁻¹ :=
        mul_le_mul_of_nonneg_right h4_le_sqrt (inv_nonneg.mpr hsqrt_pos.le)
      _ = 1 := mul_inv_cancel₀ hsqrt_pos.ne'
  have hrpow32 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / (2 : ℝ) by norm_num, Real.rpow_add hrn_pos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hcoeff_eq :
      8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) = (2 / (3 * (n : ℝ))) * (4 / Real.sqrt n) := by
    rw [hrpow32]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hcoeff_le : 8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) ≤ 2 / (3 * (n : ℝ)) := by
    calc
      8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ))
          = (2 / (3 * (n : ℝ))) * (4 / Real.sqrt n) := hcoeff_eq
      _ ≤ (2 / (3 * (n : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left hratio_le_one (by positivity)
      _ = 2 / (3 * (n : ℝ)) := mul_one _
  have hS3_nn : 0 ≤ ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ by positivity
  refine ENNReal.ofReal_le_ofReal (add_le_add_right ?_ _)
  exact mul_le_mul_of_nonneg_right hcoeff_le hS3_nn

end SteinMethod
