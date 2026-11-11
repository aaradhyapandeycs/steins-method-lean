/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.Ex36SmallNHelper

/-!
# Example 3.6 Printed Wasserstein Bound for All `n ≥ 1` (`Formalization.Leftovers.Ex36SmallN`)

Resolves Backlog Item 3 (`BL3`) and `ISSUE-3.6` in Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`, Example 3.6, `SteinIntro.tex:1053-1097`):

* `indepSum_wassersteinDist_le_ex3_6_printed` (`Ex3_6_printed`): the printed final inequality at
  `SteinIntro.tex:1089`,
  $$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
    \sqrt{\frac{2}{\pi}}\frac{\sqrt{\sum_{i=1}^n \mathbb{E}[X_i^4]}}{2n} +
    \frac{2}{3n}\sum_{i=1}^n \mathbb{E}|X_i|^3,$$
  holds unconditionally for **every** $n \ge 1$.
* `ex3_6_printed_second_term_ge_two_thirds` and `ex3_6_printed_iid_not_bigO_inv_sqrt`:
  machine-checked refutation of the post-display remark at `SteinIntro.tex:1091` (`ISSUE-3.6`),
  showing that the printed second term is always at least $\frac{2}{3}$ (and equals
  $\frac{2}{3}\mathbb{E}|X_0|^3$ in the i.i.d. case), hence cannot decay at rate $O(n^{-1/2})$.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SteinMethod

open Ex36SmallN

/-! ### Section 1: Leave-One-Out Stein Expectation Bound for `n ≥ 2` -/

/-- Leave-one-out expectation identity around $W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$
(Example 3.6, `SteinIntro.tex:1053-1097`). -/
private lemma indepSum_integral_normalSteinOp_eq_sum_looKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {f : ℝ → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hf : f ∈ normalWassersteinClass) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
    ∫ ω, normalSteinOp f (W ω) ∂P =
      ∑ i : Fin n, ∫ ω, looKernel n f (W_i i ω) (X i ω / Real.sqrt n) ∂P := by
  rcases hf with ⟨hf1, hf2, hb0, hb1, _⟩
  intro W W_i
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hX1 : ∀ i : Fin n, Integrable (X i) P := fun i ↦ integrable_of_memLp_four (hX4 i)
  have hX_sq : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 2) P :=
    fun i ↦ integrable_sq_of_memLp_four (hX4 i)
  have hW_meas : AEMeasurable W P := indepSum_aemeasurable_W hX_meas
  have hWi_meas : ∀ i : Fin n, AEMeasurable (W_i i) P := fun i ↦
    ((Finset.univ.erase i).aemeasurable_fun_sum fun j _ ↦ hX_meas j).div_const (Real.sqrt n)
  have hfW_asm := (hf1.continuous.measurable.comp_aemeasurable hW_meas).aestronglyMeasurable
  have hfWi_asm : ∀ i, AEStronglyMeasurable (fun ω ↦ f (W_i i ω)) P := fun i ↦
    (hf1.continuous.measurable.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have hdfW_asm := (hf2.continuous.measurable.comp_aemeasurable hW_meas).aestronglyMeasurable
  have hdfWi_asm : ∀ i, AEStronglyMeasurable (fun ω ↦ deriv f (W_i i ω)) P := fun i ↦
    (hf2.continuous.measurable.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have h_int_dfW : Integrable (fun ω ↦ deriv f (W ω)) P :=
    (integrable_const (Real.sqrt (2 / Real.pi))).mono' hdfW_asm
      (Filter.Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb1 (W ω))
  have h_int_dfWi : ∀ i, Integrable (fun ω ↦ deriv f (W_i i ω)) P := fun i ↦
    (integrable_const (Real.sqrt (2 / Real.pi))).mono' (hdfWi_asm i)
      (Filter.Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb1 (W_i i ω))
  have h_int_XfW : ∀ i, Integrable (fun ω ↦ X i ω * f (W ω)) P := fun i ↦
    integrable_mul_of_bound (hX1 i) hfW_asm fun ω ↦ hb0 (W ω)
  have h_int_XfWi : ∀ i, Integrable (fun ω ↦ X i ω * f (W_i i ω)) P := fun i ↦
    integrable_mul_of_bound (hX1 i) (hfWi_asm i) fun ω ↦ hb0 (W_i i ω)
  have h_int_rem2_i : ∀ i, Integrable (fun ω ↦ (X i ω ^ 2 - 1) * deriv f (W_i i ω)) P := fun i ↦ by
    have hsub : (fun ω ↦ (X i ω ^ 2 - 1) * deriv f (W_i i ω)) =
        fun ω ↦ X i ω ^ 2 * deriv f (W_i i ω) - deriv f (W_i i ω) := by ext ω; ring
    rw [hsub]
    exact (integrable_mul_of_bound (hX_sq i) (hdfWi_asm i) fun ω ↦ hb1 (W_i i ω)).sub (h_int_dfWi i)
  have h_zero_indep : ∀ (i : Fin n) (φ ψ : ℝ → ℝ), Measurable φ → Continuous ψ →
      ∫ ω, φ (X i ω) ∂P = 0 → ∫ ω, φ (X i ω) * ψ (W_i i ω) ∂P = 0 := by
    intro i φ ψ hφ hψ hmean
    let g : ℝ → ℝ := fun s ↦ ψ (s / Real.sqrt n)
    have hg_meas : Measurable g := hψ.measurable.comp (measurable_id.div_const (Real.sqrt n))
    have h_ind : IndepFun (X i) (∑ j ∈ Finset.univ.erase i, X j) P :=
      (h_indep.indepFun_finsetSum_of_notMem₀ hX_meas (Finset.notMem_erase i Finset.univ)).symm
    have hfn : (fun ω ↦ φ (X i ω) * ψ (W_i i ω)) =
        fun ω ↦ (φ ∘ X i) ω * (g ∘ ∑ j ∈ Finset.univ.erase i, X j) ω := by
      ext ω; simp [g, W_i, Finset.sum_apply]
    rw [hfn, (h_ind.comp hφ hg_meas).integral_fun_mul_eq_mul_integral
      (hφ.comp_aemeasurable (hX_meas i)).aestronglyMeasurable
      ((hψ.measurable.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
        |>.congr (Filter.Eventually.of_forall fun ω ↦ by simp [g, W_i, Finset.sum_apply]))]
    simp [hmean]
  have h_zero1 : ∀ i, ∫ ω, X i ω * f (W_i i ω) ∂P = 0 :=
    fun i ↦ h_zero_indep i id f measurable_id hf1.continuous (hX0 i)
  have h_zero2 : ∀ i, ∫ ω, (X i ω ^ 2 - 1) * deriv f (W_i i ω) ∂P = 0 := fun i ↦
    h_zero_indep i (fun s ↦ s ^ 2 - 1) (deriv f) ((measurable_id.pow_const 2).sub measurable_const)
      hf2.continuous (by rw [integral_sub (hX_sq i) (integrable_const 1), hX2 i]; simp)
  have hK_eq : ∀ (i : Fin n) (ω : Ω),
      looKernel n f (W_i i ω) (X i ω / Real.sqrt n) =
        (1 / (n : ℝ)) * deriv f (W ω) - (X i ω / Real.sqrt n) * f (W ω) +
          (X i ω / Real.sqrt n) * f (W_i i ω) +
          (1 / (n : ℝ)) * ((X i ω ^ 2 - 1) * deriv f (W_i i ω)) := by
    intro i ω; unfold looKernel
    have hW_sp : W_i i ω + X i ω / Real.sqrt n = W ω := by
      dsimp only [W, W_i]
      rw [← add_div, ← Finset.add_sum_erase Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)]; ring
    have hdiv : (X i ω / Real.sqrt n) * ((X i ω / Real.sqrt n) * deriv f (W_i i ω)) =
        (1 / (n : ℝ)) * (X i ω ^ 2 * deriv f (W_i i ω)) := by
      calc (X i ω / Real.sqrt n) * ((X i ω / Real.sqrt n) * deriv f (W_i i ω))
          = (X i ω * X i ω) / (Real.sqrt n * Real.sqrt n) * deriv f (W_i i ω) := by ring
        _ = (1 / (n : ℝ)) * (X i ω ^ 2 * deriv f (W_i i ω)) := by
            rw [Real.mul_self_sqrt hn_pos.le]; ring
    rw [hW_sp]; linear_combination hdiv
  have hK_int : ∀ i, Integrable (fun ω ↦ looKernel n f (W_i i ω) (X i ω / Real.sqrt n)) P := fun i ↦
    Integrable.congr (((h_int_dfW.const_mul _).sub
      (by simpa [div_mul_eq_mul_div] using (h_int_XfW i).div_const (Real.sqrt n))).add
      (by simpa [div_mul_eq_mul_div] using (h_int_XfWi i).div_const (Real.sqrt n))
        |>.add ((h_int_rem2_i i).const_mul _))
      (Filter.Eventually.of_forall fun ω ↦ (hK_eq i ω).symm)
  rw [← integral_finsetSum Finset.univ fun i _ ↦ hK_int i]
  have hsum_pt : (fun ω ↦ ∑ i : Fin n, looKernel n f (W_i i ω) (X i ω / Real.sqrt n)) =
      fun ω ↦ normalSteinOp f (W ω) +
        ((1 / Real.sqrt n) * ∑ i : Fin n, X i ω * f (W_i i ω) +
          (1 / (n : ℝ)) * ∑ i : Fin n, (X i ω ^ 2 - 1) * deriv f (W_i i ω)) := by
    ext ω; simp_rw [hK_eq _ ω]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hc1 : (∑ _i : Fin n, (1 / (n : ℝ)) * deriv f (W ω)) = deriv f (W ω) := by
      simp [hn_pos.ne']
    have hc2 : (∑ i : Fin n, (X i ω / Real.sqrt n) * f (W ω)) = W ω * f (W ω) := by
      dsimp [W]; rw [← Finset.sum_mul, ← Finset.sum_div]
    have hc3 : (∑ i : Fin n, (X i ω / Real.sqrt n) * f (W_i i ω)) =
        (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * f (W_i i ω) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hc1, hc2, hc3, ← Finset.mul_sum]; unfold normalSteinOp; ring
  have h_int_op : Integrable (fun ω ↦ normalSteinOp f (W ω)) P :=
    h_int_dfW.sub (integrable_mul_of_bound
      ((integrable_finsetSum Finset.univ fun i _ ↦ hX1 i).div_const (Real.sqrt n))
      hfW_asm fun ω ↦ hb0 (W ω))
  have h_int_rem1 := (integrable_finsetSum Finset.univ fun i _ ↦ h_int_XfWi i).const_mul
    (1 / Real.sqrt n)
  have h_int_rem2 := (integrable_finsetSum Finset.univ fun i _ ↦ h_int_rem2_i i).const_mul
    (1 / (n : ℝ))
  have h_int_rem12 : Integrable
      (fun ω ↦ (1 / Real.sqrt n) * (∑ i : Fin n, X i ω * f (W_i i ω)) +
        (1 / (n : ℝ)) * ∑ i : Fin n, (X i ω ^ 2 - 1) * deriv f (W_i i ω)) P :=
    h_int_rem1.add h_int_rem2
  have h_eq := congr_arg (fun g : Ω → ℝ ↦ ∫ ω, g ω ∂P) hsum_pt
  rw [integral_add h_int_op h_int_rem12, integral_add h_int_rem1 h_int_rem2,
    integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ h_int_XfWi i,
    integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ h_int_rem2_i i] at h_eq
  simp only [h_zero1, h_zero2, Finset.sum_const_zero, mul_zero, add_zero] at h_eq
  exact h_eq.symm

private lemma indepSum_wassersteinDist_le_ex3_6_of_ge_two
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn2 : 2 ≤ n) {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P) (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P) (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hZ_meas : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
          (2 * (n : ℝ)) + 2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
  intro W
  have hn : 0 < n := lt_of_lt_of_le zero_lt_two hn2
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  refine (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P'
    (indepSum_aemeasurable_W hX_meas) hZ_meas hZ_law).trans
      (iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_)
  let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
  have hexp := indepSum_integral_normalSteinOp_eq_sum_looKernel P hn hX_meas h_indep hX4 hX0 hX2 hf
  dsimp only at hexp; rw [hexp]
  obtain ⟨α, γ, hα_le, hpt⟩ := mul_abs_looKernel_le_for_ge_two hn2 hf
  have hX_sq : ∀ i, Integrable (fun ω ↦ X i ω ^ 2) P := fun i ↦ integrable_sq_of_memLp_four (hX4 i)
  have hX_cb : ∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) P :=
    fun i ↦ integrable_abs_cube_of_memLp_four (hX4 i)
  have hterm_le : ∀ i : Fin n,
      |∫ ω, looKernel n f (W_i i ω) (X i ω / Real.sqrt n) ∂P| ≤
        (1 / (n : ℝ)) * (α + 2 / 3 * ∫ ω, |X i ω| ^ 3 ∂P) := fun i ↦ by
    let M_i : Ω → ℝ := fun ω ↦ (1 / (n : ℝ)) * (α + γ * (X i ω ^ 2 - 1) + 2 / 3 * |X i ω| ^ 3)
    have hsub1 : Integrable (fun ω ↦ X i ω ^ 2 - 1) P := (hX_sq i).sub (integrable_const 1)
    have hpart1 : Integrable (fun ω ↦ α + γ * (X i ω ^ 2 - 1)) P :=
      (integrable_const α).add (hsub1.const_mul γ)
    have hMi_int : Integrable M_i P :=
      (hpart1.add ((hX_cb i).const_mul (2 / 3))).const_mul (1 / (n : ℝ))
    have hnorm := norm_integral_le_of_norm_le
      (f := fun ω ↦ looKernel n f (W_i i ω) (X i ω / Real.sqrt n)) hMi_int
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]
        have h := hpt (W_i i ω) (X i ω / Real.sqrt n)
        rw [div_mul_cancel₀ (X i ω) hsqrt_pos.ne'] at h
        simpa [M_i, one_div, inv_mul_eq_div] using (le_div_iff₀' hn_pos).mpr h)
    rw [Real.norm_eq_abs] at hnorm
    refine hnorm.trans_eq ?_
    dsimp only [M_i]
    rw [integral_const_mul, integral_add hpart1 ((hX_cb i).const_mul (2 / 3)),
      integral_add (integrable_const α) (hsub1.const_mul γ),
      integral_const_mul, integral_sub (hX_sq i) (integrable_const 1),
      integral_const_mul, integral_const, integral_const, hX2 i]
    simp only [probReal_univ, smul_eq_mul, one_mul, sub_self, mul_zero, add_zero]
  have hsum_le : |∑ i : Fin n, ∫ ω, looKernel n f (W_i i ω) (X i ω / Real.sqrt n) ∂P| ≤
      α + 2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    calc |∑ i : Fin n, ∫ ω, looKernel n f (W_i i ω) (X i ω / Real.sqrt n) ∂P|
        ≤ ∑ i : Fin n, |∫ ω, looKernel n f (W_i i ω) (X i ω / Real.sqrt n) ∂P| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, (1 / (n : ℝ)) * (α + 2 / 3 * ∫ ω, |X i ω| ^ 3 ∂P) :=
          Finset.sum_le_sum fun i _ ↦ hterm_le i
      _ = α + 2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hn_pos.ne']
  linarith [base_const_le_first_term hn hX4 hX2]

/-! ### Section 2: Direct Lipschitz Linear Shift Proof for `n = 1` -/

private lemma integral_Iic_zero_neg_mul_stdNormalPDF :
    ∫ z in Iic (0 : ℝ), (-z) * stdNormalPDF z = stdNormalPDF 0 := by
  rw [← integral_Ioi_mul_stdNormalPDF 0]
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (fun z ↦ (-z) * stdNormalPDF z) (Iic (0 : ℝ))
  have hpre : (Neg.neg ⁻¹' Iic (0 : ℝ)) = Ici 0 := by ext z; simp
  rw [← hneg, hpre, ← setIntegral_congr_set Ioi_ae_eq_Ici]
  exact setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ by simp [stdNormalPDF_even]

private lemma integral_Ioi_zero_stdNormalPDF :
    ∫ z in Ioi (0 : ℝ), stdNormalPDF z = 1 / 2 := by
  rw [← one_sub_stdNormalCDF_eq_integral_Ioi 0, stdNormalCDF_zero]; ring

private noncomputable def lipSlope (h₀ : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((∫ z in Ioi (0 : ℝ), h₀ z * stdNormalPDF z) -
    ∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z)

private lemma integrable_mul_stdNormalPDF_of_lipschitz
    {h₀ : ℝ → ℝ} (hh₀ : LipschitzWith 1 h₀) (h0 : h₀ 0 = 0) :
    Integrable (fun z ↦ h₀ z * stdNormalPDF z) volume := by
  refine integrable_mul_stdNormalPDF.abs.mono'
    (hh₀.continuous.aestronglyMeasurable.mul continuous_stdNormalPDF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z ↦ ?_)
  have hlip : |h₀ z| ≤ |z| := by simpa [Real.dist_eq, h0] using hh₀.dist_le_mul z 0
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg z),
    abs_mul, abs_of_nonneg (stdNormalPDF_nonneg z)]
  exact mul_le_mul_of_nonneg_right hlip (stdNormalPDF_nonneg z)

private lemma abs_lipShift_le_of_nonneg
    {h₀ : ℝ → ℝ} (hh₀ : LipschitzWith 1 h₀) (h0 : h₀ 0 = 0) {w : ℝ} (hw : 0 ≤ w) :
    |h₀ w - (∫ z, h₀ z * stdNormalPDF z) - lipSlope h₀ * w| ≤
      7 / 20 - (11 / 20 : ℝ) * (w ^ 2 - 1) + 2 / 3 * w ^ 3 := by
  have hlip_xy : ∀ x y : ℝ, |h₀ x - h₀ y| ≤ |x - y| := fun x y ↦ by
    simpa [Real.dist_eq] using hh₀.dist_le_mul x y
  have hlip0 : ∀ x : ℝ, |h₀ x| ≤ |x| := fun x ↦ by simpa [h0] using hlip_xy x 0
  have hint_all := integrable_mul_stdNormalPDF_of_lipschitz hh₀ h0
  have hsplit_univ : (∫ z, h₀ z * stdNormalPDF z) =
      (∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z) + ∫ z in Ioi (0 : ℝ), h₀ z * stdNormalPDF z := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint_all.integrableOn hint_all.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have hIic_le : |∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z| ≤ stdNormalPDF 0 := by
    have hdom : IntegrableOn (fun z ↦ (-z) * stdNormalPDF z) (Iic 0) := by
      simpa [neg_mul] using integrable_mul_stdNormalPDF.neg.integrableOn
    have h := norm_integral_le_of_norm_le (f := fun z ↦ h₀ z * stdNormalPDF z) hdom
      (ae_restrict_of_forall_mem measurableSet_Iic fun z hz ↦ by
        have hz' : z ≤ 0 := hz
        have h0z : |h₀ z| ≤ -z := by simpa [abs_of_nonpos hz'] using hlip0 z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg z)]
        exact mul_le_mul_of_nonneg_right h0z (stdNormalPDF_nonneg z))
    rwa [Real.norm_eq_abs, integral_Iic_zero_neg_mul_stdNormalPDF] at h
  have hIoi_le : |∫ z in Ioi (0 : ℝ), h₀ z * stdNormalPDF z| ≤ stdNormalPDF 0 := by
    have h := norm_integral_le_of_norm_le (f := fun z ↦ h₀ z * stdNormalPDF z)
      integrable_mul_stdNormalPDF.integrableOn
      (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz ↦ by
        have hz' : 0 < z := hz
        have h0z : |h₀ z| ≤ z := by simpa [abs_of_pos hz'] using hlip0 z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg z)]
        exact mul_le_mul_of_nonneg_right h0z (stdNormalPDF_nonneg z))
    rwa [Real.norm_eq_abs, integral_Ioi_mul_stdNormalPDF 0] at h
  have hp0_lt := stdNormalPDF_zero_lt
  have hp0_nn := stdNormalPDF_nonneg 0
  have hw_abs : |h₀ w| ≤ w := by simpa [abs_of_nonneg hw] using hlip0 w
  by_cases hw2 : w ≤ 2
  · have hdecomp : h₀ w - (∫ z, h₀ z * stdNormalPDF z) - lipSlope h₀ * w =
        (1 / 2 - w / 4) * h₀ w - (1 - w / 2) * (∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z) +
          (1 + w / 2) * ∫ z in Ioi (0 : ℝ), (h₀ w - h₀ z) * stdNormalPDF z := by
      have hsub_int : ∫ z in Ioi (0 : ℝ), (h₀ w - h₀ z) * stdNormalPDF z =
          h₀ w * (1 / 2) - ∫ z in Ioi (0 : ℝ), h₀ z * stdNormalPDF z := by
        have hfn : (fun z ↦ (h₀ w - h₀ z) * stdNormalPDF z) =
            fun z ↦ h₀ w * stdNormalPDF z - h₀ z * stdNormalPDF z := by ext z; ring
        rw [hfn, integral_sub (integrable_stdNormalPDF.const_mul (h₀ w)).integrableOn
          hint_all.integrableOn, integral_const_mul, integral_Ioi_zero_stdNormalPDF]
      rw [hsplit_univ, lipSlope, hsub_int]; ring
    have hdiff_Ioi : |∫ z in Ioi (0 : ℝ), (h₀ w - h₀ z) * stdNormalPDF z| ≤
        stdNormalPDF 0 - w / 2 + stdNormalPDF 0 * w ^ 2 := by
      let dom : ℝ → ℝ := fun z ↦
        (z - w) * stdNormalPDF z + Set.indicator (Ioc 0 w) (fun u ↦ 2 * (w - u) * stdNormalPDF 0) z
      have hdom1 : IntegrableOn (fun z ↦ (z - w) * stdNormalPDF z) (Ioi 0) := by
        have hfn : (fun z ↦ (z - w) * stdNormalPDF z) =
            fun z ↦ z * stdNormalPDF z - w * stdNormalPDF z := by ext z; ring
        rw [hfn]; exact integrable_mul_stdNormalPDF.integrableOn.sub
          (integrable_stdNormalPDF.const_mul w).integrableOn
      have hdom2 : IntegrableOn
          (Set.indicator (Ioc 0 w) (fun u ↦ 2 * (w - u) * stdNormalPDF 0)) (Ioi 0) :=
        ((integrable_indicator_iff measurableSet_Ioc).mpr
          (((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const)
            |>.integrableOn_Ioc)).integrableOn
      have hdom : IntegrableOn dom (Ioi 0) := hdom1.add hdom2
      have hnorm := norm_integral_le_of_norm_le
        (f := fun z ↦ (h₀ w - h₀ z) * stdNormalPDF z) hdom
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdNormalPDF_nonneg z)]
          refine (mul_le_mul_of_nonneg_right (hlip_xy w z) (stdNormalPDF_nonneg z)).trans ?_
          dsimp only [dom]
          by_cases hzw : z ≤ w
          · have hmem : z ∈ Ioc 0 w := ⟨hz, hzw⟩
            rw [Set.indicator_of_mem hmem, abs_of_nonneg (sub_nonneg.mpr hzw)]
            nlinarith [stdNormalPDF_le_zero z, sub_nonneg.mpr hzw]
          · rw [Set.indicator_of_notMem (fun hm : z ∈ Ioc 0 w ↦ hzw hm.2), add_zero,
              abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hzw))])
      rw [Real.norm_eq_abs] at hnorm
      refine hnorm.trans_eq ?_
      dsimp only [dom]; rw [integral_add hdom1 hdom2]
      have hev1 : ∫ z in Ioi (0 : ℝ), (z - w) * stdNormalPDF z = stdNormalPDF 0 - w / 2 := by
        have hfn : (fun z ↦ (z - w) * stdNormalPDF z) =
            fun z ↦ z * stdNormalPDF z - w * stdNormalPDF z := by ext z; ring
        rw [hfn, integral_sub integrable_mul_stdNormalPDF.integrableOn
          (integrable_stdNormalPDF.const_mul w).integrableOn,
          integral_Ioi_mul_stdNormalPDF 0, integral_const_mul, integral_Ioi_zero_stdNormalPDF]; ring
      have hev2 : ∫ z in Ioi (0 : ℝ),
          Set.indicator (Ioc 0 w) (fun u ↦ 2 * (w - u) * stdNormalPDF 0) z =
            stdNormalPDF 0 * w ^ 2 := by
        rw [setIntegral_indicator measurableSet_Ioc,
          inter_eq_self_of_subset_right Ioc_subset_Ioi_self, ← intervalIntegral.integral_of_le hw]
        let Q : ℝ → ℝ := fun u ↦ -(w - u) ^ 2 * stdNormalPDF 0
        have hd : ∀ u ∈ Set.uIcc 0 w, HasDerivAt Q (2 * (w - u) * stdNormalPDF 0) u := fun u _ ↦
          (((((hasDerivAt_const u w).sub (hasDerivAt_id u)).pow 2).neg).mul_const
            (stdNormalPDF 0)).congr_deriv (by dsimp; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          (((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const)
            |>.intervalIntegrable 0 w)]
        dsimp [Q]; ring
      rw [hev1, hev2]
    have htri : |h₀ w - (∫ z, h₀ z * stdNormalPDF z) - lipSlope h₀ * w| ≤
        2 * stdNormalPDF 0 - (1 / 2 - stdNormalPDF 0) * w ^ 2 + stdNormalPDF 0 / 2 * w ^ 3 := by
      rw [hdecomp]
      have hc1 : 0 ≤ 1 / 2 - w / 4 := by linarith
      have hc2 : 0 ≤ 1 - w / 2 := by linarith
      have hc3 : 0 ≤ 1 + w / 2 := by linarith
      have ht1 : |(1 / 2 - w / 4) * h₀ w| ≤ (1 / 2 - w / 4) * w := by
        rw [abs_mul, abs_of_nonneg hc1]; exact mul_le_mul_of_nonneg_left hw_abs hc1
      have ht2 : |(1 - w / 2) * ∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z| ≤
          (1 - w / 2) * stdNormalPDF 0 := by
        rw [abs_mul, abs_of_nonneg hc2]; exact mul_le_mul_of_nonneg_left hIic_le hc2
      have ht3 : |(1 + w / 2) * ∫ z in Ioi (0 : ℝ), (h₀ w - h₀ z) * stdNormalPDF z| ≤
          (1 + w / 2) * (stdNormalPDF 0 - w / 2 + stdNormalPDF 0 * w ^ 2) := by
        rw [abs_mul, abs_of_nonneg hc3]; exact mul_le_mul_of_nonneg_left hdiff_Ioi hc3
      linarith [abs_sub ((1 / 2 - w / 4) * h₀ w)
        ((1 - w / 2) * ∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z),
        abs_add_le ((1 / 2 - w / 4) * h₀ w -
          (1 - w / 2) * ∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z)
          ((1 + w / 2) * ∫ z in Ioi (0 : ℝ), (h₀ w - h₀ z) * stdNormalPDF z)]
    have hid : (7 / 20 - (11 / 20 : ℝ) * (w ^ 2 - 1) + 2 / 3 * w ^ 3) -
        (4 / 5 - 1 / 10 * w ^ 2 + 1 / 5 * w ^ 3) =
        149 / 3920 + (w - 9 / 14) ^ 2 * (7 / 15 * w + 3 / 20) := by ring
    have hnn : 0 ≤ 149 / 3920 + (w - 9 / 14) ^ 2 * (7 / 15 * w + 3 / 20) := by positivity
    have hw3 : 0 ≤ w ^ 3 := pow_nonneg hw 3
    nlinarith [sq_nonneg w]
  · have hw_gt : 2 < w := lt_of_not_ge hw2
    have htot_le : |∫ z, h₀ z * stdNormalPDF z| ≤ 2 * stdNormalPDF 0 := by
      rw [hsplit_univ]; exact (abs_add_le _ _).trans (by linarith)
    have hslope_le : |lipSlope h₀ * w| ≤ stdNormalPDF 0 * w := by
      rw [abs_mul, abs_of_nonneg hw]
      refine mul_le_mul_of_nonneg_right ?_ hw
      unfold lipSlope; rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [abs_sub (∫ z in Ioi (0 : ℝ), h₀ z * stdNormalPDF z)
        (∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z)]
    have htri : |h₀ w - (∫ z, h₀ z * stdNormalPDF z) - lipSlope h₀ * w| ≤
        2 * stdNormalPDF 0 + (1 + stdNormalPDF 0) * w := by
      linarith [abs_sub (h₀ w) (∫ z, h₀ z * stdNormalPDF z),
        abs_sub (h₀ w - ∫ z, h₀ z * stdNormalPDF z) (lipSlope h₀ * w)]
    set u : ℝ := w - 2
    have hu : 0 ≤ u := sub_nonneg.mpr hw_gt.le
    have hid : (7 / 20 - (11 / 20 : ℝ) * (w ^ 2 - 1) + 2 / 3 * w ^ 3) - (4 / 5 + 7 / 5 * w) =
        13 / 30 + 22 / 5 * u + 69 / 20 * u ^ 2 + 2 / 3 * u ^ 3 := by dsimp [u]; ring
    have hnn : 0 ≤ 13 / 30 + 22 / 5 * u + 69 / 20 * u ^ 2 + 2 / 3 * u ^ 3 := by positivity
    nlinarith

private lemma abs_lipShift_le
    {h₀ : ℝ → ℝ} (hh₀ : LipschitzWith 1 h₀) (h0 : h₀ 0 = 0) (w : ℝ) :
    |h₀ w - (∫ z, h₀ z * stdNormalPDF z) - lipSlope h₀ * w| ≤
      7 / 20 - (11 / 20 : ℝ) * (w ^ 2 - 1) + 2 / 3 * |w| ^ 3 := by
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw]; exact abs_lipShift_le_of_nonneg hh₀ h0 hw
  · let g₀ : ℝ → ℝ := fun z ↦ h₀ (-z)
    have hg₀_lip : LipschitzWith 1 g₀ := LipschitzWith.of_dist_le_mul fun x y ↦ by
      have hd := hh₀.dist_le_mul (-x) (-y)
      rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq,
        show -x - -y = -(x - y) by ring, abs_neg, ← Real.dist_eq, ← Real.dist_eq] at hd
      simpa [g₀] using hd
    have hg0 : g₀ 0 = 0 := by simp [g₀, h0]
    have htot_eq : (∫ z, g₀ z * stdNormalPDF z) = ∫ z, h₀ z * stdNormalPDF z := by
      have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding (fun z ↦ h₀ z * stdNormalPDF z)
      simpa [g₀, stdNormalPDF_even] using hneg
    have hslope_eq : lipSlope g₀ = -lipSlope h₀ := by
      have h1 : (∫ z in Ioi (0 : ℝ), g₀ z * stdNormalPDF z) =
          ∫ z in Iic (0 : ℝ), h₀ z * stdNormalPDF z := by
        have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
          (Homeomorph.neg ℝ).measurableEmbedding (fun z ↦ h₀ z * stdNormalPDF z) (Iic (0 : ℝ))
        rw [← hneg, show Neg.neg ⁻¹' Iic (0 : ℝ) = Ici 0 by ext z; simp,
          ← setIntegral_congr_set Ioi_ae_eq_Ici]
        exact setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ by simp [g₀, stdNormalPDF_even]
      have h2 : (∫ z in Iic (0 : ℝ), g₀ z * stdNormalPDF z) =
          ∫ z in Ioi (0 : ℝ), h₀ z * stdNormalPDF z := by
        have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
          (Homeomorph.neg ℝ).measurableEmbedding (fun z ↦ h₀ z * stdNormalPDF z) (Ioi (0 : ℝ))
        rw [← hneg, show Neg.neg ⁻¹' Ioi (0 : ℝ) = Iio 0 by ext z; simp,
          setIntegral_congr_set Iio_ae_eq_Iic]
        exact setIntegral_congr_fun measurableSet_Iic fun z _ ↦ by simp [g₀, stdNormalPDF_even]
      unfold lipSlope; rw [h1, h2]; ring
    have h := abs_lipShift_le_of_nonneg hg₀_lip hg0 (neg_nonneg.mpr hw)
    have hlhs : g₀ (-w) - (∫ z, g₀ z * stdNormalPDF z) - lipSlope g₀ * (-w) =
        h₀ w - (∫ z, h₀ z * stdNormalPDF z) - lipSlope h₀ * w := by
      rw [htot_eq, hslope_eq]; dsimp [g₀]; rw [neg_neg]; ring
    rw [hlhs, show (-w) ^ 2 = w ^ 2 by ring, ← abs_of_nonpos hw] at h
    exact h

private lemma indepSum_wassersteinDist_le_ex3_6_one
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Fin 1 → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin 1, AEMeasurable (X i) P) (hX4 : ∀ i : Fin 1, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin 1, ∫ ω, X i ω ∂P = 0) (hX2 : ∀ i : Fin 1, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hZ_meas : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin 1, X i ω) / Real.sqrt (1 : ℕ)
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin 1, ∫ ω, X i ω ^ 4 ∂P) /
          (2 * ((1 : ℕ) : ℝ)) + 2 / (3 * ((1 : ℕ) : ℝ)) * ∑ i : Fin 1, ∫ ω, |X i ω| ^ 3 ∂P) := by
  intro W
  have _ := hZ_meas
  have hW_eq : W = X 0 := by ext ω; simp [W]
  have hW_meas : AEMeasurable W P := hW_eq ▸ hX_meas 0
  have hW4 : MemLp W 4 P := hW_eq ▸ hX4 0
  have hW0 : ∫ ω, W ω ∂P = 0 := hW_eq ▸ hX0 0
  have hW2 : ∫ ω, W ω ^ 2 ∂P = 1 := hW_eq ▸ hX2 0
  have hW1_int := integrable_of_memLp_four hW4
  have hW2_int := integrable_sq_of_memLp_four hW4
  have hW3_int := integrable_abs_cube_of_memLp_four hW4
  unfold wassersteinDist
  refine ipm_le fun h hh hIntW hIntZ ↦ ENNReal.ofReal_le_ofReal ?_
  let h₀ : ℝ → ℝ := fun x ↦ h x - h 0
  have hh₀_lip : LipschitzWith 1 h₀ := by simpa [h₀] using hh.sub (LipschitzWith.const (h 0))
  have hh0 : h₀ 0 = 0 := sub_self (h 0)
  have hh₀_comp_int : Integrable (fun ω ↦ h₀ (W ω)) P :=
    ((integrable_map_measure hh.continuous.aestronglyMeasurable hW_meas).mp hIntW).sub
      (integrable_const (h 0))
  have hh₀_std_int : Integrable h₀ stdNormalLaw :=
    (hZ_law ▸ hIntZ : Integrable h stdNormalLaw).sub (integrable_const (h 0))
  set c : ℝ := ∫ z, h₀ z * stdNormalPDF z
  have hc_eq : stdNormalExpect h₀ = c := by
    rw [stdNormalExpect_eq_integral_mul_pdf]
    exact integral_congr_ae (ae_of_all _ fun _ ↦ mul_comm _ _)
  have hdiff_eq : (∫ x, h x ∂(P.map W)) - (∫ z, h z ∂(P'.map Z)) =
      ∫ ω, (h₀ (W ω) - c - lipSlope h₀ * W ω) ∂P := by
    rw [integral_map hW_meas hh.continuous.aestronglyMeasurable, hZ_law]
    have hc_law : ∫ z, h₀ z ∂stdNormalLaw = c := hc_eq
    have hz_split : (∫ z, h z ∂stdNormalLaw) = c + h 0 := by
      rw [show (fun z ↦ h z) = fun z ↦ h₀ z + h 0 from funext fun z ↦ (sub_add_cancel _ _).symm,
        integral_add hh₀_std_int (integrable_const (h 0)), hc_law, integral_const]; simp
    have hw_split : (∫ ω, h (W ω) ∂P) = (∫ ω, h₀ (W ω) ∂P) + h 0 := by
      rw [show (fun ω ↦ h (W ω)) = fun ω ↦ h₀ (W ω) + h 0 from
        funext fun _ ↦ (sub_add_cancel _ _).symm,
        integral_add hh₀_comp_int (integrable_const (h 0)), integral_const]; simp
    have hh₀c_int : Integrable (fun ω ↦ h₀ (W ω) - c) P := hh₀_comp_int.sub (integrable_const c)
    rw [hw_split, hz_split, integral_sub hh₀c_int (hW1_int.const_mul (lipSlope h₀)),
      integral_sub hh₀_comp_int (integrable_const c), integral_const,
      integral_const_mul, hW0, mul_zero]; simp
  rw [hdiff_eq]
  let M : Ω → ℝ := fun ω ↦ 7 / 20 - (11 / 20 : ℝ) * (W ω ^ 2 - 1) + 2 / 3 * |W ω| ^ 3
  have hW2_sub : Integrable (fun ω ↦ W ω ^ 2 - 1) P := hW2_int.sub (integrable_const 1)
  have hM_part1 : Integrable (fun ω ↦ (7 / 20 : ℝ) - (11 / 20 : ℝ) * (W ω ^ 2 - 1)) P :=
    (integrable_const (7 / 20 : ℝ)).sub (hW2_sub.const_mul (11 / 20))
  have hM_int : Integrable M P := hM_part1.add (hW3_int.const_mul (2 / 3))
  have hnorm := norm_integral_le_of_norm_le
    (f := fun ω ↦ h₀ (W ω) - c - lipSlope h₀ * W ω) hM_int
    (Filter.Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_lipShift_le hh₀_lip hh0 (W ω))
  rw [Real.norm_eq_abs] at hnorm
  have hM_eval : ∫ ω, M ω ∂P = 7 / 20 + 2 / 3 * ∫ ω, |X 0 ω| ^ 3 ∂P := by
    dsimp only [M]
    rw [integral_add hM_part1 (hW3_int.const_mul (2 / 3)),
      integral_sub (integrable_const (7 / 20 : ℝ)) (hW2_sub.const_mul (11 / 20)),
      integral_const_mul, integral_sub hW2_int (integrable_const 1),
      integral_const_mul, integral_const, integral_const, hW2, hW_eq]; simp
  have hα : (7 / 20 : ℝ) ≤ Real.sqrt (2 / Real.pi) / (2 * Real.sqrt (1 : ℕ)) := by
    simp only [Nat.cast_one, Real.sqrt_one, mul_one]; linarith [sqrt_two_div_pi_gt]
  have hfirst := base_const_le_first_term (by decide : 0 < 1) hX4 hX2
  have hsum3 : (∑ i : Fin 1, ∫ ω, |X i ω| ^ 3 ∂P) = ∫ ω, |X 0 ω| ^ 3 ∂P := Fin.sum_univ_one _
  simp only [Nat.cast_one, mul_one, hsum3] at hfirst ⊢
  linarith [hnorm, hM_eval, hα, hfirst]

/-! ### Section 3: Main Theorem (`Ex3_6_printed` for All `n ≥ 1`) and `L1091` Rate Refutation -/

/-- **Example 3.6, printed Wasserstein bound for all `n ≥ 1`** (`SteinIntro.tex:1053-1097`,
eq. at `L1089`; resolving `ISSUE-3.6` for $1 \le n < 16$): for independent mean-zero,
unit-variance random variables $X_1, \dots, X_n \in L^4(P)$ ($n \ge 1$) and
$W = (\sum_{i=1}^n X_i)/\sqrt{n}$,
$$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \sqrt{\frac{2}{\pi}}\frac{\sqrt{\sum_{i=1}^n \mathbb{E}[X_i^4]}}{2n} +
  \frac{2}{3n}\sum_{i=1}^n \mathbb{E}|X_i|^3.$$ -/
theorem indepSum_wassersteinDist_le_ex3_6_printed
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1)
    (hZ_meas : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
  have hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1 :=
    fun i ↦ integral_sq_eq_one_of_variance (hX_meas i) (hX0 i) (hX_var i)
  by_cases hn2 : 2 ≤ n
  · exact indepSum_wassersteinDist_le_ex3_6_of_ge_two P P' hn2 hX_meas h_indep hX4 hX0 hX2
      hZ_meas hZ_law
  · have hn1 : n = 1 := by omega
    subst hn1
    exact indepSum_wassersteinDist_le_ex3_6_one P P' hX_meas hX4 hX0 hX2 hZ_meas hZ_law

/-- Universal lower bound $\frac{2}{3} \le \frac{2}{3n}\sum_{i=1}^n \mathbb{E}|X_i|^3$ on the
printed second term of Example 3.6 (`SteinIntro.tex:1089-1091`; `ISSUE-3.6`). -/
theorem ex3_6_printed_second_term_ge_two_thirds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) :
    (2 / 3 : ℝ) ≤ 2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum_ge : (n : ℝ) ≤ ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := Finset.sum_le_sum fun i _ ↦
          one_le_integral_abs_cube (hX4 i)
            (integral_sq_eq_one_of_variance (hX_meas i) (hX0 i) (hX_var i))
  have hmul := mul_le_mul_of_nonneg_left hsum_ge (by positivity : 0 ≤ 2 / (3 * (n : ℝ)))
  have hcancel : 2 / (3 * (n : ℝ)) * (n : ℝ) = 2 / 3 := by field_simp [hn_pos.ne']
  linarith

/-- Machine-checked refutation of the i.i.d. $O(n^{-1/2})$ remark at `SteinIntro.tex:1091`
(`ISSUE-3.6`): for any identically distributed sequence $(X_k)_{k \ge 0}$ with
$\mathbb{E}[X_0] = 0$, $\operatorname{Var}(X_0) = 1$, and $X_0 \in L^4(P)$, the printed second
term at `L1089` equals $\frac{2}{3}\mathbb{E}|X_0|^3 \ge \frac{2}{3}$ for every $n \ge 1$ and is
**not** bounded by $C / \sqrt{n}$ for any $C \in \mathbb{R}$. -/
theorem ex3_6_printed_iid_not_bigO_inv_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (h_ident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 0) P P)
    (hX0_meas : AEMeasurable (X 0) P)
    (hX0_4 : MemLp (X 0) 4 P)
    (hX0_mean : ∫ ω, X 0 ω ∂P = 0)
    (hX0_var : ProbabilityTheory.variance (X 0) P = 1) :
    (∀ n : ℕ, 0 < n →
      2 / (3 * (n : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) =
        2 / 3 * ∫ ω, |X 0 ω| ^ 3 ∂P) ∧
      ¬ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
        2 / (3 * (n : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) ≤ C / Real.sqrt n := by
  have h_eq3 : ∀ k : ℕ, ∫ ω, |X k ω| ^ 3 ∂P = ∫ ω, |X 0 ω| ^ 3 ∂P := fun k ↦
    ((h_ident k).comp (continuous_abs.pow 3).measurable).integral_eq
  have h_const : ∀ n : ℕ, 0 < n →
      2 / (3 * (n : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) =
        2 / 3 * ∫ ω, |X 0 ω| ^ 3 ∂P := fun n hn ↦ by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    simp_rw [h_eq3]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn_pos.ne']
  refine ⟨h_const, ?_⟩
  rintro ⟨C, hC⟩
  have h1 := one_le_integral_abs_cube hX0_4
    (integral_sq_eq_one_of_variance hX0_meas hX0_mean hX0_var)
  let m : ℕ := Nat.ceil (max C 0 * 2) + 1
  let N : ℕ := m * m
  have hm_pos : 0 < m := Nat.succ_pos _
  have hN_pos : 0 < N := Nat.mul_pos hm_pos hm_pos
  have hsqrtN : Real.sqrt N = (m : ℝ) := by
    dsimp [N]; rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg m)]
  have hm_gt : max C 0 * 2 < (m : ℝ) := by
    dsimp [m]; push_cast; linarith [Nat.le_ceil (max C 0 * 2)]
  have hC_lt : C / Real.sqrt N < 1 / 2 := by
    rw [hsqrtN, div_lt_iff₀ (Nat.cast_pos.mpr hm_pos)]; linarith [le_max_left C 0]
  have hle := hC N hN_pos
  rw [h_const N hN_pos] at hle; linarith

end SteinMethod
